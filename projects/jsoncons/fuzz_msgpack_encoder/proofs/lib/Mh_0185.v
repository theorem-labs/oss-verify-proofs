(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0185_blobs1 Mh_0185_blobs2.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module PnSrcSFillP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSrcSFillP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelK47Corelib4Init5Logic3and01C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP6KS_fbEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallK47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP9KS_fbE_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP6KS_fbAC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP4PfbA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP9KS_fbA_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP7KS_fbB1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP:KS_fbB1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP7KS_fbB2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB2<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP5PfbB23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP:KS_fbB2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PMSFBP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_004 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_005 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_006 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_007 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_008 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_009 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_010 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_011 ())). Qed.
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
Module PfbE := BndP_Ns_045.LibSegNs_fbE.
Definition KS_fbE : list nat := Eval vm_compute in (BG.kept_list 48 PfbE.regs0 PfbE.regs_out0).
Lemma KS_fbE_ok : BG.kept_ok 48 PfbE.regs0 PfbE.regs_out0 KS_fbE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_012 ())). Qed.
Lemma fbE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 32)) -> 140735332483104 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 ->
  (((V 2%nat) - 32) + 32 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 32)) -> L5.img_clear M 65536 814272 -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 800392 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 800152 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 2 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x47114 M) (st fx' R' 0x471e0 M')
        /\ (forall x, In x KS_fbE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 120
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_013 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PfbA := BndP_Ns_045.LibSegNs_fbA.
Definition KS_fbA : list nat := Eval vm_compute in (BG.kept_list 48 PfbA.regs0 PfbA.regs_out0).
Lemma KS_fbA_ok : BG.kept_ok 48 PfbA.regs0 PfbA.regs_out0 KS_fbA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_014 ())). Qed.
Lemma fbA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 32)) -> 140735332483104 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 ->
  (((V 2%nat) - 32) + 32 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 32)) -> L5.img_clear M 65536 814272 -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 800392 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 800152 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x47114 M) (st fx' R' 0x6ba54 M')
        /\ (forall x, In x KS_fbA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 291168
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 440916
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_015 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PfbB1 := BndP_Ns_045.LibSegNs_fbB1.
Definition KS_fbB1 : list nat := Eval vm_compute in (BG.kept_list 48 PfbB1.regs0 PfbB1.regs_out0).
Lemma KS_fbB1_ok : BG.kept_ok 48 PfbB1.regs0 PfbB1.regs_out0 KS_fbB1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_016 ())). Qed.
Lemma fbB1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 16384 -> getr R (reg 18) = Z_to_bv 64 16384 ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 32)) -> 140735332483104 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 ->
  (((V 2%nat) - 32) + 32 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 32)) -> L5.img_clear M 65536 814272 -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 800392 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 800152 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x47160 M) (st fx' R' 0x471e0 M')
        /\ (forall x, In x KS_fbB1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_017 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PfbB2 := BndP_Ns_045.LibSegNs_fbB2.
Definition KS_fbB2 : list nat := Eval vm_compute in (BG.kept_list 48 PfbB2.regs0 PfbB2.regs_out0).
Lemma KS_fbB2_ok : BG.kept_ok 48 PfbB2.regs0 PfbB2.regs_out0 KS_fbB2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_018 ())). Qed.
Lemma fbB2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 16384 ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 32)) -> 140735332483104 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 ->
  (((V 2%nat) - 32) + 32 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 32)) -> L5.img_clear M 65536 814272 -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 37%nat) + 16) -> L5.u64_at RSEGS M (V 37%nat) 800392 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 800152 -> L5.u32_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 160) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> 0 <= (V 35%nat) <= 16383 -> L5.writable RSEGS M ((V 37%nat) + 152) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> ~ (((V 37%nat) + 152) <= bv_unsigned a < ((V 37%nat) + 152) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> ~ (((V 37%nat) + 152) <= i < ((V 37%nat) + 152) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x47160 M) (st fx' R' 0x471e0 M')
        /\ (forall x, In x KS_fbB2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) + 152) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSFillP ()) [] (Mh_0185_blobs1.kr_b_019 ())). Qed.
(* [comment removed for export] *)

End PMSFBP.

End PnSrcSFillP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0185 () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List9app_nil_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib7Mh_0106;PnParSpecsS5PMPSS;xsgetn_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloI69OSSVerify5KrLib7Mh_00905PgSrc3PGS8owner_ok00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_fill_bufferC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS9fill_argsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP4no_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmParSpecs4PMPS8fill_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6W_srcGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6oo_layC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6oo_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_vp_issC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_strbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_classic_impC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_iss_iosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8zeros_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS7W_srcfGC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK:heap_nodupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_egC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM4sm_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4strm01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR7inW_nilC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK;fst_neq_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_01358PmParKit4PMPKAblocks_apart_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK3dkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_winC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK;defined_dkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6oo_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP8fbA_concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;ek_of_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8iss_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;outside_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP<base_ok_keepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK@iss_unread_whereC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK;iss_size_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5ag_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>agree_on_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFRBoutside_of_not_inWC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP9fbB1_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6sub_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP9fbB2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9ek_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6ag_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK9dkr_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK=dkr_hpres_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK9dkr_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7iss_updC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP8fbE_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5cs_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGSAfill_buffer_specGC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega6VarMap1t02C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00907PmModel2PM7iosb_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP6KS_fbAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r369d8_369dc7W_47198C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r369d8_369dc7F_47198C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r369d8_369dc7D_47198C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01I47Corelib7Numbers7BinNums8positive00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I69OSSVerify5KrLib7Mh_00905PgSrc3PGS5owner00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP7KS_fbB1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP7KS_fbB2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185;PnSrcSFillP6PMSFBP6KS_fbEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS;tbfill_argsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmTxtSpecs5PMTXS8tbfill_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmTxtSpecs5PMTXS:tbfill_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6oo_winC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK9dkr_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGSDfill_buffer_tb_specGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5err_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN4mownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9mrest_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_skC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_off_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ8qa_off_aC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_tranC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_sbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR3o_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR3o_vC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5enc_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN6o_sinkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5aeownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5m16_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6m8_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN9gs_post_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN6W_mrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN7pot_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8with_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM;mparser_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_bbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86v8_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4p_tbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8mgrow_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR<make_ec_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS2gmC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3BR0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3wokC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS6WS_wokC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8WS_casesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS7ec_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS@ec_state_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_doneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7p_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7mvec_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_errcat_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5ec_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8own_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01247PnMpKit4PQMK9untouchedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01247PnMpKit4PQMK<mparser_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;mp_gsE_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN8mrun_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR6minv_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN9mprog_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF3dkrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5gs_ekC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indc69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS9rest_keptC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01024PnV84PQV82v802C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01247PnMpKit4PQMK@mparser_more_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout?pa_errcat_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PnQKeep4PQKP;err_ok_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8ec_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_off_isC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_off_vC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout;ne_off_sinkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_off_vrefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_off_ecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS6WS_runC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS4FINWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS7gs_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01247PnMpKit4PQMK8set_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP9KS_mp_gsEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8lbx_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3PSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6OFF_TBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6OFF_BBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_STKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5PSIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_SRCC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4mpst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8chunk_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8OFF_MAXDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r4124c_413b47W_46ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r4124c_413b47F_46ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r4124c_413b47D_46ba8C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV82v800C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z2gtC69OSSVerify5KrLib7Mh_00905PgSrc3PGS>src_read_specGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR7gs_typeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z9land_onesC46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<mp_gsFm_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8gm_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<mp_gsFa_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT196_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN8gs_classC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5READ1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT197_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5READ2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT198_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5READ4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT199_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT200_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT201_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT212_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT213_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT214_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT215_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT216_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT217_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT218_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT219_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT220_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT221_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT222_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP>mp_gsT223_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3OKPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP:KS_mp_gsFmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP:KS_mp_gsFaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT196C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT197C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT198C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT199C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT200C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT201C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT212C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT213C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT214C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT215C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT216C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT217C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT218C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT219C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT220C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT221C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT222C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP<KS_mp_gsT223C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5AL_opC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5AL_ecC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbI46Stdlib9micromega7EnvRing3Pol00K46Stdlib9micromega=RingMicromega5Psatz07c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqc69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD2rqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT;ecap_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdE0_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT8al8_itemC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:vdE1w_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdE1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4cinvC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz05c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdE0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdE1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP8KS_vdE1wC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3COKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic3iffC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP8vdA_concC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0Jc69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD8st_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX7fsd_runC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdA3_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC59OSSVerify5KrLib7Mh_00387FPSteps8frm_zeroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP8vdB_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX@regupd_other_idxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX?regupd_same_idxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphc69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdCd_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD8rq_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdDd_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD7rq_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD6r_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdWd_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD7ev_tailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD8ro_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD9mid_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdCf_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdWf_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9vdJf_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC59OSSVerify5KrLib7Mh_00367SpinAlg6srz_fzC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX<fcvt_dyn_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX8fcmp_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX9fsgnj_runC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdA3C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_4040cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty05K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty06C49OSSVerify5KrLibDNs0_code_3fce0_410347F_4040cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_4040cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6KS_vdBC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40414C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40414C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40414C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40418C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fcmpop01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40418C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40418C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40444C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr6fsgnop01C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40444C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40444C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdDdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40458C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40458C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40458C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40434C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr4ffmt01C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40434C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40434C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6KS_vdAC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40400C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40400C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40400C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40404C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40404C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40404C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdCdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdWdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdCfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdWfC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdJfC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses;subrelationC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List:in_app_iffC47Corelib7Program6Basics4implC69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK6sp_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_nmaxC1?~~~~~~~~~~~~~~~C47Corelib9RelationsDRelation_Definitions8relationC69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7alignedC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@subrelation_reflC69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_endC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pot_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK6is_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;brange_inclC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK>u32_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:enEAa_concC1?~~~~~~~~~~~~~~~K47Corelib4Init6Specif7sumbool01K47Corelib4Init6Specif7sumbool02c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK:enc_at_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT=sink_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT>ec_state_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEA3cslC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK:cmp_run_EAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:enEAc_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEA7wall_ecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEA8wall_errC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT8enc_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT9sink_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:enEAr_concC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decc69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEA3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5>writable_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;enEAp1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_rc69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP<enEAp2w_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;enEAp2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec8Z_le_decC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT<ek_piece_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsBsubrelation_properc69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEA3CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEArC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEAp2C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEAaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEAcC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC49OSSVerify5KrLibDNs0_code_3fce0_410347W_3ff30C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3ff30C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3ff30C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEAp1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:KS_enEAp2wC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveK69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eend02C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eend00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eend01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:enEOa_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEO3cslC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK:cmp_run_EOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:enEOc_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEO7wall_ecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEO8wall_errC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:enEOr_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEO3finC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;enEOp1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP<enEOp2w_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;enEOp2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEO3CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEOrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEOp2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEOaC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEOcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_4070cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_4070cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_4070cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEOp1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:KS_enEOp2wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU642wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_tagC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU643cslC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU642rqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_u64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuE0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuE1w_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuE1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU643CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuE0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuE1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40124C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40124C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40124C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_ESECC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuE1wC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU643COKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU646wboundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuA7_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU647rq_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU647ev_tailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuA8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU646r_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU648st_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuB8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU648rq_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU649mid_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuA16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuB16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU645jtailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU648ro_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuA32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuB32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuA64_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuB64_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuA5_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuA7C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuA8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuA16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuA32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuA64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuA5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuB8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuB16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuB32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuB64C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7view_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3cslC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8wsA_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV6CSLsubC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout?ne_validate_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0103;PnCValSpecW6PECVSWBvalidate_fun_specWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59frame_butC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_01356PmStep3PMK?hi_heap_stretchC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV7CSLcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV8st_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsH31_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV4at_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;wsH255_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP<wsH255b_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsH16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsW16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsH32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsW32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsH31C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9KS_wsH255C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:KS_wsH255bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsH16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsW16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsH32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsW32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3COKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_xsgetnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP9xgA0_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6hio_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_01358PmParKit4PMPKBiss_unread_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP9xgA1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP9xgA2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove5PMCPS;memmove_runC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP9xgC1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP9xgC2_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r5b260_5b2647W_6bb14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r5b260_5b2647F_6bb14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r5b260_5b2647D_6bb14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgA1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgA2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgA0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgC2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgC1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST7tcreditC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L2svC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnIface6debitRC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Heap7HnIface7refundRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9PnTsWs2DA8PQTSW2DA2q1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB5XPostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L5thiscC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L5savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L4strLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB2VXC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L6tcellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L5lregsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L4strCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS7ts_textC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST7ws_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP:twtD0_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib7Mh_00906L5Core3L5C;fresh_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01037PnHeapR4PMSR=refund_debitRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9PnTsWs2DA8PQTSW2DA8ag_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9PnTsWs2DA8PQTSW2DA8ag_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L:strC_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01828PnTsWs2Q7PQTSW2Q5u_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01828PnTsWs2Q7PQTSW2Q5zbv_uC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP:twtD1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST;tcredit_preC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L<text_of_strCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L8fin_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L3ctxC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS7WRS_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8KS_twtD0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8KS_twtD1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L5MAGICC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01037PnHeapR4PMSR9OPDEL_SCRC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib7Mh_0020ENs0_code_r418a8_418ac7W_46e40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r418a8_418ac7F_46e40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r418a8_418ac7D_46e40C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflK69OSSVerify5KrLib7Mh_00846L5Defs2L56bstore02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00846L5Defs2L56bigobj01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56big_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55bo_fbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56bo_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5:hull_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55bo_stC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib7Mh_02618PnTsWs2L7PQTSW2L7mem_ok0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6PnTsWs5PQTSW7capx_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6PnTsWs5PQTSW<odd_byte_bitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG=u8_of_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9PnTsWs2DA8PQTSW2DA5dynfbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP:twhD0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBfresh_block_boundsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP;twhD1L_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB8dynfb_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB:heap_swap2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specc69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB5div1DC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP8KS_twhD0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9KS_twhD1LC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00846L5Defs2L56bigobj00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB3HfbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01037PnHeapR4PMSR9OPNEW_SCRC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00846L5Defs2L56bstore00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB:tcredit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9credit_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG<u8_of_u64_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6PnTsWs5PQTSW<bit0_of_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6PnTsWs5PQTSW9land255_0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Peano2le01K47Corelib4Init5Peano2le02C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01037PnHeapR4PMSR<debitR_smallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP;twhD1S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01828Ns0Opnew5L5NEW8opnew_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opnew_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB<debit_debitRC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?mul_mod_distr_lC69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP9tw2S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP9tw3S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9KS_twhD1SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw2SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw3SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPNEW_SCRC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3oddC56Stdlib6ZArith6BinInt1Z=odd_add_mul_2C56Stdlib6ZArith6BinInt1Z8bit0_oddC69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP;twhD1M_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_addC69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP9tw2M_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP9tw3M_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01828Ns0Opdel5L5DEL8opdel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opdel_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=hpres_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP9tw4M_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0197:PnTsWs2DHP9PQTSW2DHP9KS_twhD1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw2MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw3MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01979PnTsWs2HP8PQTSW2HP7KS_tw4MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vw_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_ovC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP5kept8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6memrelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR12W0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP3midC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8consumedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6saves4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP5rregsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP9src_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vo_srcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP9own_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8spF_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8spG_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP7src_updC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6sub_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86pot_v8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP6KS_spFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP6KS_spGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r41030_410347W_46874C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r41030_410347F_46874C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r41030_410347D_46874C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV87v8_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8spS_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV88v8_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86v8_capC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01067PnV8Kit5PQV8K6apart2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vo_updC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms;ProperProxyC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<iss_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP9base_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV8@srd_read_v_specGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV87v8_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP:kept_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C:hpres_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6inW_W0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8spE_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK>src_step_transC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK69OSSVerify5KrLib7Mh_01024PnV84PQV82v801C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP6KS_spSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP6KS_spEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01067PnV8Kit5PQV8K<src_of_vw_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV89src_of_vwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP9spR0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP5SLOWKC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<app_inv_headC69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR1;outside_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK;ek_drop_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8spB_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP:outside_W0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP5FASTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP9KS_spR0_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP9KS_spR0_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8KS_spB_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8KS_spB_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8spA_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rc69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP3R0KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8KS_spA_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8KS_spA_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8KS_spA_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01829PnV8SpanP6PQVSPP8KS_spA_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR13IHtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16memrelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR18state_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16saves8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16lstateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR15lregsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR14acctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR15kept7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6mu_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR19unread_nnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Srd56PQVSR59u8_of_u32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP9svH0_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16sub_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd36PQVSR35rpathC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd46PQVSR45dpathC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16finishC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP9svH1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP9KS_svH0_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP9KS_svH0_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP9KS_svH0_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP7KS_svH1C1?~~~~~~~~~~~~~~~".
Module Ns0PgSrcFill.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnParSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSrcSFillP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019.Ns0_code_r369d8_369dc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Local Ltac lia := L5FastLia.plia.

Module PGSFB.
Import PMS.

Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
  apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Theorem fill_buffer_okG : PMPSS.xsgetn_spec L HI -> PGS.fill_buffer_specG RSEGS AD L HI.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_020 ())). Qed.

End WithHeap.
End PGSFB.

End Ns0PgSrcFill.
Module Ns0PgSrcFillTb.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnParSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmTxtSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSrcSFillP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019.Ns0_code_r369d8_369dc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Local Ltac lia := L5FastLia.plia.

Module PGSFBT.
Import PMS.

Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
  apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Theorem fill_buffer_tb_okG : PMPSS.xsgetn_spec L HI -> PGS.fill_buffer_tb_specG RSEGS AD L HI.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_021 ())). Qed.

End WithHeap.
End PGSFBT.

End Ns0PgSrcFillTb.
Module PnErrSP.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnErrSP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP6KS_erAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP9KS_erA_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerA6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP6KS_erBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01857PnErrSP5PMERP4PerB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP9KS_erB_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PMERP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_022 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_023 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_024 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_025 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_026 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_027 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_028 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_029 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_030 ())). Qed.
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
Module PerA := BndP_Ns_045.LibSegNs_erA.
Definition KS_erA : list nat := Eval vm_compute in (BG.kept_list 48 PerA.regs0 PerA.regs_out0).
Lemma KS_erA_ok : BG.kept_ok 48 PerA.regs0 PerA.regs_out0 KS_erA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_031 ())). Qed.
Lemma erA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332483200 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 140735332483200 <= (V 33%nat) <= 140737488355312 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 16 <= ((V 2%nat) - 128)) -> L5.writable RSEGS M (V 33%nat) 16 -> 1 <= (V 34%nat) <= 64 ->
  L5.u8_at RSEGS M 880208 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41a54 M) (st fx' R' 0x41aa8 M')
        /\ (forall x, In x KS_erA -> getr R' (reg x) = getr R (reg x))
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) 813840
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_032 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PerB := BndP_Ns_045.LibSegNs_erB.
Definition KS_erB : list nat := Eval vm_compute in (BG.kept_list 48 PerB.regs0 PerB.regs_out0).
Lemma KS_erB_ok : BG.kept_ok 48 PerB.regs0 PerB.regs_out0 KS_erB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_033 ())). Qed.
Lemma erB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332483200 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 140735332483200 <= (V 33%nat) <= 140737488355312 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 16 <= ((V 2%nat) - 128)) -> L5.writable RSEGS M (V 33%nat) 16 -> 1 <= (V 34%nat) <= 64 ->
  L5.img_clear M 65536 814272 -> L5.img_clear M 880208 880210 -> L5.writable RSEGS M 880208 2 -> L5.img_clear M 1018008 1018016 ->
  L5.u32_at RSEGS M 1018016 1 -> L5.img_clear M 1018020 1018024 -> L5.u64_at RSEGS M 1018024 1018032 -> L5.img_clear M 1018032 1018040 ->
  L5.img_clear M 1018048 1018296 -> L5.img_clear M 1018304 1018552 -> L5.writable RSEGS M 1018008 544 -> L5.img_clear M 1018595 1018596 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 16) -> ~ ((0 + 880208) <= bv_unsigned a < (0 + 880208) + 2) -> ~ ((0 + 1018016) <= bv_unsigned a < (0 + 1018016) + 4) -> ~ ((0 + 1018048) <= bv_unsigned a < (0 + 1018048) + 8) -> ~ ((0 + 1018304) <= bv_unsigned a < (0 + 1018304) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 16) -> ~ ((0 + 880208) <= i < (0 + 880208) + 2) -> ~ ((0 + 1018016) <= i < (0 + 1018016) + 4) -> ~ ((0 + 1018048) <= i < (0 + 1018048) + 8) -> ~ ((0 + 1018304) <= i < (0 + 1018304) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41a54 M) (st fx' R' 0x41aa8 M')
        /\ (forall x, In x KS_erB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) 813840
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 34%nat)
        /\ L5.u8_at RSEGS M' 880209 1
        /\ L5.u8_at RSEGS M' 880208 1
        /\ L5.u32_at RSEGS M' 1018016 2
        /\ L5.u64_at RSEGS M' 1018304 813840
        /\ L5.u64_at RSEGS M' 1018048 415036).
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrSP ()) [] (Mh_0185_blobs1.kr_b_034 ())). Qed.
(* [comment removed for export] *)

End PMERP.

End PnErrSP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.
Module PnErrS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnCertKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnErrSP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r363e8_363ec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnErrS () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List2InK47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib7Mh_0106:PnCertKitS4PMCK8cs_in_KSC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic5False00c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP6KS_erAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP6KS_erBC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_errcat_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5ec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5err_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout:pa_make_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z3divK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib7Mh_0106:PnCertKitS4PMCK5lb_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout?pa_errcat_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_drv_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_errcat_dtorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ<qa_drv_guardC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP8erA_concC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01856PnErrS5PMERR6cs_erAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106:PnCertKitS4PMCK:u32_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST<atexit_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106:PnCertKitS4PMCK<writable_imgC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec8Z_lt_decI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01857PnErrSP5PMERP8erB_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout?pa_syscat_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout;pa_loc_footC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout7pm_footC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01426PnKitS4PMKS:cwr_foot_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01856PnErrS5PMERR6cs_erBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR<make_ec_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST9atexit_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0020ENs0_code_r363e8_363ec7W_41a60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r363e8_363ec7F_41a60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r363e8_363ec7D_41a60C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:addrs_wf_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01856PnErrS5PMERR9wseg_errgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01856PnErrS5PMERR;wseg_atexitC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMERR.
Abbreviation AQ := PnLayoutQS.QADDR_S.
Import PMS.

Lemma wseg_errg : wseg_ok RSEGS (Z_to_bv 64 880208) (Z.to_nat 2) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrS ()) [] (Mh_0185_blobs1.kr_b_035 ())). Qed.
Lemma wseg_atexit : wseg_ok RSEGS (Z_to_bv 64 1018008) (Z.to_nat 544) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrS ()) [] (Mh_0185_blobs1.kr_b_036 ())). Qed.
Lemma cs_erA : forall k, In k PMK.cs_all -> In k PMERP.KS_erA.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrS ()) [] (Mh_0185_blobs1.kr_b_037 ())). Qed.
Lemma cs_erB : forall k, In k PMK.cs_all -> In k PMERP.KS_erB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrS ()) [] (Mh_0185_blobs1.kr_b_038 ())). Qed.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Theorem make_ec_ok : PQR.make_ec_spec RSEGS AD AQ L HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnErrS ()) ["Stage"] (Mh_0185_blobs1.kr_b_039 ())). Qed.

End Stage.
End PMERR.

End PnErrS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LeanFeed2. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0186.
Module PnMpSGetSize.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0186. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.PnMpOwner OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnMpKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnRunN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnMpKitN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0186.PnMpSGetSizeP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019.Ns0_code_r4124c_413b4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnMpSGetSize () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5ec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib7Mh_00188PmLayout=pa_errcat_objC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;hl_alloc_roC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK:heap_nodupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN4mownC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applC46Stdlib5Lists4List4inclC46Stdlib5Lists4List9incl_apprC46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9mrest_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5aeownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8own_inclC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3BR0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8lbx_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK;fst_neq_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPKAblocks_apart_heapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3ND0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic5False00c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8WS_casesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega5Tauto8GFormula07c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS8chunk_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib7Mh_01028PnQModel3PQM;mparser_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN6W_mrunC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_01356PmStep3PMK?inW_not_outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK;ek_drop_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7dk_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS4OWNFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR4o_tbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR4o_bbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR5o_stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR4o_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5err_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR3o_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9adaptor_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR3o_vC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5enc_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN6o_sinkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_off_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_off_isC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7OFF_SRCC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic6or_indc69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3wokC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5ag_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS7aown_neC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01247PnMpKit4PQMK9untouchedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnMpKitN4PNMK7ae_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ASIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnMpKitN4PNMK=ec_state_keepC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_01246PnRunN4PNRN8gs_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS2gmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8with_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS9rest_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS6WS_wokC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS7ec_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_egC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM4sm_gC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8mgrow_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6p_moreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3cplC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4acctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5oacctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6eboundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3balC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR6minv_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN9mprog_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3nlvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib7Mh_01028NemModel3NEM3phiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5p_stkC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ8qa_off_aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_off_vC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout;ne_off_sinkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_off_vrefC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_off_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN9gs_post_dC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS4FINWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN7pot_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r4124c_413b47W_46ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r4124c_413b47F_46ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019ENs0_code_r4124c_413b47D_46ba8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_01028PnQModel3PQM6mstate00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS6WS_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS>src_read_specGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS8ly_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9src_ownerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6hio_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5m16_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6m8_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01039PnMpOwner4PQOW<src_owner_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00905PgSrc3PGS8owner_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS7dst_okGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_winC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmParSpecs4PMPS8read_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6W_srcGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS7W_srcfGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFRBoutside_of_not_inWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP<base_ok_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout?pa_errcat_guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PnQKeep4PQKP;err_ok_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS>src_step_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00905PgSrc3PGS5owner00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5PSIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR<make_ec_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6sub_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP=mp_gsR1o_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS3OKPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP=mp_gsR1e_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS4ERRPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS2RDC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;KS_mp_gsR1oC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;KS_mp_gsR1eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5AL_opC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS5AL_ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP=mp_gsR2o_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP=mp_gsR2e_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;KS_mp_gsR2oC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;KS_mp_gsR2eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP=mp_gsR4o_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP=mp_gsR4e_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;KS_mp_gsR4oC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0186=PnMpSGetSizeP7PQMPGSP;KS_mp_gsR4eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;ek_of_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR7inW_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01247PnMpKit4PQMK<mparser_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF;with_src_idC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_tranC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8iss_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;outside_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9ek_weakenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4mpst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR7gs_typeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8frame_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN8margs_gsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN8mrun_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_get_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185<PnMpSGetSize5PQMGS4walkC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN=get_size_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR3o_pC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnQRun3PQR4o_isC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN4GS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01246PnRunN4PNRN8TSRES_MEC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQMGS.
Import PMS.
Abbreviation AQ := PnLayoutQS.QADDR_S.
Abbreviation AE := NemLayoutS.NEADDR_S.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Lemma ec_agree M M' o v c : L5C.agree_on M M' o 16 -> 0 <= o -> o + 16 <= 2 ^ 64 -> PMSP.ec_at RSEGS M o v c -> PMSP.ec_at RSEGS M' o v c.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_040 ())). Qed.

Lemma ec_state_defined M o (bb : bool) c : NEM.ec_state RSEGS AD M o bb c -> L5.defined M o 16.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_041 ())). Qed.

(* [comment removed for export] *)
Lemma gs_step LB cr (fx fx1 : FPState) R R1 (pc pc1 : Z) M M1 model K (sp x n : Z) :
  hi_heap HI LB cr M (m_vmmaps model) -> m_halted model = None -> m_vm_lazy model = [] -> 0x7fff80000000 <= hl_sptop L ->
  hl_ceil L <= sp - 48 -> sp <= hl_sptop L -> (n = 0 \/ (hl_ceil L <= x /\ x + n <= hl_sptop L)) ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 pc1) M1 (seg_rom RSEGS)) -> mem_grows M M1 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (x <= i < x + n) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  (hi_heap HI LB cr M1 (m_vmmaps model) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_042 ())). Qed.
Lemma gs_ek LB (sp x n : Z) W M M1 :
  (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> ~ (x <= i < x + n) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  L5C.stk (hl_sptop L) M sp 22528 -> PMFR.brange L LB -> (forall a, x <= a < x + n -> PMK.inW W a) ->
  PMK.ek L LB sp 22528 W M M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_043 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Run.
Variables (R : bvmap 5 word) (M0 : word -> option byte) (model : Model) (K : TSet) (LBX : list (Z * Z)) (cr : credit)
          (sp r fb cat n d t : Z) (s : PQM.mpst) (st : NEM.aest) (str : PM.vstr) (sm : PM.strm) (e b : bool).
Let LB : list (Z * Z) := PNRN.mown s st ++ LBX.
Let op : Z := fb + 32.
Let ois : Z := fb + 616.
Let src0 : PM.srcst := PQM.p_src s.
Let WS : list L5.range := PGS.W_srcG (op + 24) ois src0.
(* [comment removed for export] *)
Abbreviation ae_at := (NEM.ae_at RSEGS AD AE L PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).

Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis Rra : getr R (PMK.reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp : getr R (PMK.reg 2) = Z_to_bv 64 sp.
Hypothesis Rgp : getr R (PMK.reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp : getr R (PMK.reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 sp 22528.
Hypothesis F1 : sp <= fb.
Hypothesis F2 : fb + 928 <= hl_sptop L.
Hypothesis F3 : fb mod 16 = 0.
Hypothesis PA0 : PQM.mparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) M0 op ois s.
Hypothesis AE0 : ae_at M0 (fb + 432) (fb + 536) (fb + 592) st.
Hypothesis IA0 : PM.iss_at RSEGS AD PMSP.T3 M0 ois str sm.
Hypothesis VREF0 : L5.u64_at RSEGS M0 (op + 496) (fb + 432).
Hypothesis BASE0 : PMST.base_ok RSEGS AD M0.
Hypothesis ERR0 : PQST.err_ok RSEGS AD AQ M0 e.
Hypothesis GROW0 : PQM.mgrow_ok s.
Hypothesis AOK0 : NEM.ae_ok st.
Hypothesis CPL0 : PQM.cpl s (NEM.ae_a st).
Hypothesis ACCT0 : PQM.acct n s (NEM.ae_a st) sm.
Hypothesis OACCT0 : NEM.oacct n s st sm.
Hypothesis EB0 : NEM.ebound st.
Hypothesis BAL0 : b = false -> NEM.bal st.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis INV : PQR.minv_d d s.
Hypothesis EC0 : NEM.ec_state RSEGS AD M0 (fb + 8) b cat.
Hypothesis Ht : PQR.gs_type t.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PQM.mpst) (st' : NEM.aest)
            (sm' : PM.strm) (e' b' : bool) (cr' : credit),
        regs_preserved R R' ->
        PNRN.gs_post_d RSEGS AD AQ AE L d t R' M' fb s s' st st' str sm sm' e e' b b' cat n ->
        L5C.hpres L LBX sp (PMSP.pm_scr 5) (PNRN.W_mrun AD AQ AE fb) M0 M' ->
        PMSP.credit_keep cr cr' (PNRN.pot_run L s st) (PNRN.pot_run L s' st') ->
        model_but_vm model model' -> hi_heap HI (PNRN.mown s' st' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition gm (M1 : word -> option byte) (src1 : PM.srcst) (sm1 : PM.strm) : Prop :=
  PQM.mparser_at RSEGS AD PMSP.T3 PMSP.T4 (pa_vp_parser AD) M1 op ois (PQM.with_src s src1)
  /\ PM.iss_at RSEGS AD PMSP.T3 M1 ois str sm1 /\ PMST.base_ok RSEGS AD M1 /\ PQST.err_ok RSEGS AD AQ M1 e
  /\ PMSP.src_step src0 src1 sm sm1
  /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ PMK.ek L LB sp 22528 WS M0 M1 /\ PMK.dk L LB sp 22528 M0 M1 /\ L5C.stk (hl_sptop L) M1 sp 22528 /\ hi_heap HI LB cr M1 (m_vmmaps model).


(* [comment removed for export] *)
Lemma BR0 : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_044 ())). Qed.
Lemma ND0 : NoDup (map fst LB).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_045 ())). Qed.
Lemma own_incl : incl (PNRN.mown s st) LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_046 ())). Qed.
Lemma lbx_incl : incl LBX LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_047 ())). Qed.
Lemma chunk_in : In (PM.sr_qc src0, PM.CHUNK) LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_048 ())). Qed.
(* [comment removed for export] *)
Lemma OWNF : forall B m, In (B, m) (PNRN.mown s st) -> B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
               forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_049 ())). Qed.
(* [comment removed for export] *)
Lemma WS_cases a : PMK.inW WS a -> (fb + 312 <= a < fb + 352) \/ (fb + 656 <= a < fb + 664) \/ (fb + 768 <= a < fb + 772)
                                   \/ (PM.sr_qc src0 <= a < PM.sr_qc src0 + PM.CHUNK).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_050 ())). Qed.
(* [comment removed for export] *)
Lemma WS_frame a : fb <= a < fb + 928 -> ~ (fb + 312 <= a < fb + 352) -> ~ (fb + 656 <= a < fb + 664) -> ~ (fb + 768 <= a < fb + 772) ->
  ~ PMK.inW WS a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_051 ())). Qed.
(* [comment removed for export] *)
Lemma WS_blk B m : In (B, m) LB -> B <> PM.sr_qc src0 -> forall i, B <= i < B + m -> ~ PMK.inW WS i.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_052 ())). Qed.
(* [comment removed for export] *)
Lemma aown_ne B m : In (B, m) (NEM.aeown st) -> B <> PM.sr_qc src0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_053 ())). Qed.

(* [comment removed for export] *)
Lemma FINW M3 W3 : PMK.ek L LB sp 22528 W3 M0 M3 -> PMK.dk L LB sp 22528 M0 M3 -> L5C.stk (hl_sptop L) M3 sp 22528 ->
  (forall a, PMK.inW W3 a -> PMK.inW (PNRN.W_mrun AD AQ AE fb) a \/ (PM.sr_qc src0 <= a < PM.sr_qc src0 + PM.CHUNK)) ->
  L5C.hpres L LBX sp 22528 (PNRN.W_mrun AD AQ AE fb) M0 M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_054 ())). Qed.
(* [comment removed for export] *)
Lemma WS_run a : PMK.inW WS a -> PMK.inW (PNRN.W_mrun AD AQ AE fb) a \/ (PM.sr_qc src0 <= a < PM.sr_qc src0 + PM.CHUNK).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_055 ())). Qed.

(* [comment removed for export] *)
Definition wok (a : Z) : Prop :=
  (fb + 312 <= a < fb + 352) \/ (fb + 656 <= a < fb + 664) \/ (fb + 768 <= a < fb + 772) \/ (PM.sr_qc src0 <= a < PM.sr_qc src0 + PM.CHUNK)
  \/ (fb + 8 <= a < fb + 24) \/ (fb + 40 <= a < fb + 41) \/ (hl_img_lo L <= a < hl_img_hi L).
Lemma WS_wok a : PMK.inW WS a -> wok a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_056 ())). Qed.
(* [comment removed for export] *)
Lemma rest_kept M1 W3 : PMK.ek L LB sp 22528 W3 M0 M1 -> (forall a, PMK.inW W3 a -> wok a) ->
  ae_at M1 (fb + 432) (fb + 536) (fb + 592) st /\ L5.u64_at RSEGS M1 (op + 496) (fb + 432).
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_057 ())). Qed.
Lemma ec_kept M1 W3 : PMK.ek L LB sp 22528 W3 M0 M1 -> (forall a, PMK.inW W3 a -> wok a /\ ~ (fb + 8 <= a < fb + 24)) ->
  NEM.ec_state RSEGS AD M1 (fb + 8) b cat.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_058 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OKP (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (src1 : PM.srcst) (sm1 : PM.strm) (gsb : Z) :
  getr R1 (PMK.reg 1) = getr R (PMK.reg 1) -> (forall x, In x PMK.cs_all -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
  PNRN.gs_class t (bv_unsigned (getr R1 (PMK.reg 10))) gsb -> PM.unread src1 sm1 <= PM.unread src0 sm - gsb ->
  gm M1 src1 sm1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x46bf0 M1 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_059 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ERRP (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (v : Z) (src1 : PM.srcst) (sm1 : PM.strm) :
  getr R1 (PMK.reg 1) = Z_to_bv 64 0x46bd4 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (PMK.reg 8) = Z_to_bv 64 op ->
  getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 11) = Z_to_bv 64 v ->
  (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) -> 1 <= v <= 64 ->
  PQR.make_ec_spec RSEGS AD AQ L HI ->
  gm M1 src1 sm1 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x41a54 M1 model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_060 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma src_step_trans (s1 s2 s3 : PM.srcst) (m1 m2 m3 : PM.strm) :
  PMSP.src_step s1 s2 m1 m2 -> PMSP.src_step s2 s3 m2 m3 -> PMSP.src_step s1 s3 m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_061 ())). Qed.

Lemma RD (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (src1 : PM.srcst) (sm1 : PM.strm) (q k rr : Z) :
  getr R1 (PMK.reg 1) = Z_to_bv 64 rr -> L5.ra_ok rr -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) ->
  getr R1 (PMK.reg 10) = Z_to_bv 64 (op + 24) -> getr R1 (PMK.reg 11) = Z_to_bv 64 q -> getr R1 (PMK.reg 12) = Z_to_bv 64 k ->
  getr R1 (PMK.reg 3) = getr R (PMK.reg 3) -> getr R1 (PMK.reg 4) = getr R (PMK.reg 4) ->
  sp - 48 <= q -> q + k <= sp - 32 -> 1 <= k <= 4 ->
  PGS.src_read_specG RSEGS AD L HI ->
  gm M1 src1 sm1 ->
  (forall (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) (src2 : PM.srcst) (sm2 : PM.strm) (dd : Z),
      regs_preserved R1 R2 -> getr R2 (PMK.reg 10) = Z_to_bv 64 dd -> 0 <= dd <= k ->
      PM.unread src2 sm2 = PM.unread src1 sm1 - dd ->
      gm M2 src2 sm2 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 rr M2 model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x4629c M1 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_062 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac gsfeed AL1 AL2 := first [ PMK.sc | unfold PQMPGSP.aligned; first [exact AL1 | exact AL2 | assumption] ].

Lemma AL_op : op mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_063 ())). Qed.
Lemma AL_ec : (fb + 8) mod 8 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_064 ())). Qed.

Local Ltac read_tail ko ke k rr R1 :=
  intros X1 X2 X8 X9 X10 X11 X12 X18 KS1 GC SR MKE GM1;
  apply (RD _ _ _ _ _ _ _ _ X1 ltac:(split; [lia| reflexivity]) X2 X10 X11 X12 ltac:(apply KS1; PMK.inl) ltac:(apply KS1; PMK.inl)
           ltac:(lia) ltac:(lia) ltac:(lia) SR GM1);
  intros fx2 R2 M2 src2 sm2 dd RP2 Y10 Hd UN2 GM2;
  pose proof GM2 as (_ & _ & BASE2 & _ & _ & S8 & S16 & S24 & S32 & _ & _ & STK2 & _);
  pose proof MOK as (Mh & Ml & Mm); pose proof STK2 as (A16 & SLO & SHI & STOP & SD2);
  pose proof (L5C.stk_writable RSEGS _ M2 sp 22528 STK2) as WR2;
  pose proof BASE2 as (IMG2 & _); cbn [pa_rw_lo AD PnLayoutS.ADDR_S] in IMG2;
  pose proof AL_op as ALo; pose proof AL_ec as ALe;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18;
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18;
  assert (R2_2 : getr R2 (PMK.reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (PMK.cs_of_preserved R1 R2 2%nat RP2) by PMK.inl; exact X2);
  assert (R2_8 : getr R2 (PMK.reg 8) = Z_to_bv 64 op) by (rewrite (PMK.cs_of_preserved R1 R2 8%nat RP2) by PMK.inl; exact X8);
  assert (R2_9 : getr R2 (PMK.reg 9) = Z_to_bv 64 (fb + 8)) by (rewrite (PMK.cs_of_preserved R1 R2 9%nat RP2) by PMK.inl; exact X9);
  assert (R2_18 : getr R2 (PMK.reg 18) = Z_to_bv 64 k) by (rewrite (PMK.cs_of_preserved R1 R2 18%nat RP2) by PMK.inl; exact X18);
  assert (R2x : forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (PMK.reg x) = getr R (PMK.reg x));
  [ intros x Hx; rewrite (PMK.cs_of_preserved R1 R2 x RP2) by (revert x Hx; apply (PMPK.sub_in PMK.cs_all); vm_compute; reflexivity); apply KS1; exact Hx |];
  destruct (Z.eq_dec dd k) as [Dk|Dk];
  [ subst dd;
    pose proof (LF2CBN( ko fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => fb + 8
                 | 40%nat => bv_unsigned (getr R (PMK.reg 1)) | 41%nat => bv_unsigned (getr R (PMK.reg 8)) | 42%nat => bv_unsigned (getr R (PMK.reg 9))
                 | 43%nat => bv_unsigned (getr R (PMK.reg 18)) | _ => 0 end) )) as P;
    PMK.feed P ltac:(gsfeed ALo ALe);
    destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3 & T1 & T2 & T8 & T9 & T18);
    assert (M3 = M2) as -> by (apply functional_extensionality; exact FR3);
    apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 rr R3 0x46ba8 M2 K Mh Ml MS3);
    rewrite PMPK.word_id in T1, T8, T9, T18;
    apply (OKP fx3 R3 M2 src2 sm2 k T1); [| | unfold src0 in *; lia | exact GM2];
    [ intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [first [ rewrite T2; symmetry; exact Rsp | assumption | (rewrite (KS3 _) by PMK.inl; apply R2x; PMK.inl) ] |]); destruct Hx
    | apply GC; pose proof (bv_unsigned_in_range 64 (getr R3 (PMK.reg 10))) as BB; change (bv_modulus 64) with (2 ^ 64) in BB; lia ]
  | pose proof (LF2CBN( ke fx2 R2 M2 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => fb + 8 | 33%nat => dd | _ => 0 end) )) as P;
    PMK.feed P ltac:(first [ gsfeed ALo ALe | (rewrite Y10; reflexivity) ]);
    destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3 & T1 & T10 & T11);
    assert (M3 = M2) as -> by (apply functional_extensionality; exact FR3);
    apply (PMK.spiece_ro RSEGS model fx2 fx3 R2 rr R3 0x41a0c M2 K Mh Ml MS3);
    apply (ERRP fx3 R3 M2 1 src2 sm2 T1); try assumption;
    [ rewrite (KS3 2%nat) by PMK.inl; exact R2_2 | rewrite (KS3 8%nat) by PMK.inl; exact R2_8 | rewrite (KS3 9%nat) by PMK.inl; exact R2_9
    | intros x Hx; rewrite (KS3 x) by (revert x Hx; apply (PMPK.sub_in _); vm_compute; reflexivity); apply R2x; exact Hx | lia ] ].

Lemma READ1 (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  getr R1 (PMK.reg 1) = Z_to_bv 64 0x46bbc -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (PMK.reg 8) = Z_to_bv 64 op ->
  getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (op + 24) -> getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 33) ->
  getr R1 (PMK.reg 12) = Z_to_bv 64 1 -> getr R1 (PMK.reg 18) = Z_to_bv 64 1 ->
  (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
  (forall len, 0 <= len -> PNRN.gs_class t len 1) -> PGS.src_read_specG RSEGS AD L HI -> PQR.make_ec_spec RSEGS AD AQ L HI -> gm M1 src0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x4629c M1 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_065 ())). Qed.
Lemma READ2 (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  getr R1 (PMK.reg 1) = Z_to_bv 64 0x46b34 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (PMK.reg 8) = Z_to_bv 64 op ->
  getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (op + 24) -> getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 36) ->
  getr R1 (PMK.reg 12) = Z_to_bv 64 2 -> getr R1 (PMK.reg 18) = Z_to_bv 64 2 ->
  (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
  (forall len, 0 <= len -> PNRN.gs_class t len 2) -> PGS.src_read_specG RSEGS AD L HI -> PQR.make_ec_spec RSEGS AD AQ L HI -> gm M1 src0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x4629c M1 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_066 ())). Qed.
Lemma READ4 (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  getr R1 (PMK.reg 1) = Z_to_bv 64 0x46b68 -> getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (PMK.reg 8) = Z_to_bv 64 op ->
  getr R1 (PMK.reg 9) = Z_to_bv 64 (fb + 8) -> getr R1 (PMK.reg 10) = Z_to_bv 64 (op + 24) -> getr R1 (PMK.reg 11) = Z_to_bv 64 (sp - 40) ->
  getr R1 (PMK.reg 12) = Z_to_bv 64 4 -> getr R1 (PMK.reg 18) = Z_to_bv 64 4 ->
  (forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x)) ->
  (forall len, 0 <= len -> PNRN.gs_class t len 4) -> PGS.src_read_specG RSEGS AD L HI -> PQR.make_ec_spec RSEGS AD AQ L HI -> gm M1 src0 sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x4629c M1 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_067 ())). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gm_entry (M1 : word -> option byte) :
  mem_grows M0 M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 48 <= i < sp - 48 + 48) -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)) ->
  hi_heap HI LB cr M1 (m_vmmaps model) ->
  L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) -> L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) ->
  L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) -> L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) ->
  gm M1 src0 sm.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_068 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ret_case conc t0 fx :=
  pose proof MOK as (Mh0 & Ml0 & _);
  pose proof (LF2CBN( conc fx R M0 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => fb + 8 | 33%nat => t0 | _ => 0 end) )) as P;
  PMK.feed P ltac:(first [ gsfeed AL_op AL_ec | lia ]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & REST);
  apply (gs_step LB cr fx fx1 R R1 0x46a90 0x46ba8 M0 M1 model K sp 0 0 HH0 Mh0 Ml0 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(left; reflexivity)
           MS1 MG1 (fun i Hi N1 _ => FRZ1 i Hi N1));
  intros HH1;
  let A0 := fresh "A0" in
  lazymatch type of REST with
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ => destruct REST as (A0 & _ & _ & ?C32 & ?C24 & ?C16 & ?C8)
  | _ /\ _ /\ _ /\ _ /\ _ /\ _ => destruct REST as (A0 & _ & ?C32 & ?C24 & ?C16 & ?C8)
  end;
  apply (OKP fx1 R1 M1 src0 sm 0);
  [ rewrite (KS1 1%nat) by PMK.inl; reflexivity
  | intros x Hx; rewrite (KS1 x) by (revert x Hx; apply (PMPK.sub_in _); vm_compute; reflexivity); reflexivity
  | lazymatch goal with
    | |- PNRN.gs_class _ (bv_unsigned ?w) _ =>
        lazymatch type of A0 with
        | bv_unsigned _ = Z.land _ 15 => rewrite A0; change (Z.land t 15) with (Z.land t (Z.ones 4)); rewrite Z.land_ones by lia;
                                         pose proof (Z.mod_pos_bound t (2 ^ 4) ltac:(lia)) as MB; unfold PNRN.gs_class; lia
        | _ = Z_to_bv 64 _ => rewrite A0; rewrite L5.unsigned_lit by lia; unfold PNRN.gs_class; lia
        end
    end
  | lia
  | apply (gm_entry M1 MG1 (fun i Hi N => FRZ1 i Hi N) HH1); assumption ].
Local Ltac read_case conc t0 fx RDL :=
  pose proof MOK as (Mh0 & Ml0 & _);
  pose proof (LF2CBN( conc fx R M0 (fun j => match j with 2%nat => sp | 36%nat => op | 37%nat => fb + 8 | 33%nat => t0 | _ => 0 end) )) as P;
  PMK.feed P ltac:(first [ gsfeed AL_op AL_ec | lia ]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & REST);
  apply (gs_step LB cr fx fx1 R R1 0x46a90 0x46254 M0 M1 model K sp 0 0 HH0 Mh0 Ml0 ltac:(lia) ltac:(unfold hl_ceil; lia) ltac:(lia) ltac:(left; reflexivity)
           MS1 MG1 (fun i Hi N1 _ => FRZ1 i Hi N1));
  intros HH1;
  destruct REST as (X1 & X2 & X8 & X9 & X10 & X11 & X12 & X13 & X18 & C32 & C24 & C16 & C8);
  apply (RDL fx1 R1 M1 X1 X2 X8 X9); [ rewrite X10; f_equal; unfold op; lia | rewrite X11; f_equal; lia | exact X12 | exact X18
    | intros x Hx; rewrite (KS1 x) by (revert x Hx; apply (PMPK.sub_in _); vm_compute; reflexivity); reflexivity
    | intros len Hlen; unfold PNRN.gs_class; lia
    | assumption | assumption | apply (gm_entry M1 MG1 (fun i Hi N => FRZ1 i Hi N) HH1 C32 C24 C16 C8) ].

Lemma walk (fx : FPState) :
  getr R (PMK.reg 10) = Z_to_bv 64 op -> getr R (PMK.reg 11) = Z_to_bv 64 t -> getr R (PMK.reg 12) = Z_to_bv 64 (fb + 8) ->
  PGS.src_read_specG RSEGS AD L HI -> PQR.make_ec_spec RSEGS AD AQ L HI ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x46ad8 M0 model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Run"] (Mh_0185_blobs1.kr_b_069 ())). Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem get_size_ok : PGS.src_read_specG RSEGS AD L HI -> PQR.make_ec_spec RSEGS AD AQ L HI -> PNRN.get_size_spec RSEGS AD AQ AE L HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnMpSGetSize ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_070 ())). Qed.

End WithHeap.
End PQMGS.

End PnMpSGetSize.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155.
Module PnSEncDblP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncDblP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6KS_vdAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA3NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9KS_vdA_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdA6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdA3C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA3<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdA33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdA3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6KS_vdBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9KS_vdB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdCdC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCd3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdCd_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdCfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdCf3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdCf_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdDdC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdDd3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdDd_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdWfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWf3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdWf_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdWdC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdWd3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdWd_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdJfC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdJf3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdJf_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdE0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdE0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7KS_vdE1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE13NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP:KS_vdE1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP5PvdE16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP8KS_vdE1wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP;KS_vdE1w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6PvdE1w6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6KS_vdZC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP4PvdZ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP9KS_vdZ_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSENCDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_071 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_072 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_073 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_074 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_075 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_076 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_077 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_078 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_079 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_080 ())). Qed.
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
Module PvdA := BndP_Ns_113.LibSegNs_vdA.
Definition KS_vdA : list nat := Eval vm_compute in (BG.kept_list 60 PvdA.regs0 PvdA.regs_out0).
Lemma KS_vdA_ok : BG.kept_ok 60 PvdA.regs0 PvdA.regs_out0 KS_vdA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_081 ())). Qed.
Lemma vdA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40438 M) (st fx' R' 0x40448 M')
        /\ (forall x, In x KS_vdA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_082 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdA3 := BndP_Ns_113.LibSegNs_vdA3.
Definition KS_vdA3 : list nat := Eval vm_compute in (BG.kept_list 60 PvdA3.regs0 PvdA3.regs_out0).
Lemma KS_vdA3_ok : BG.kept_ok 60 PvdA3.regs0 PvdA3.regs_out0 KS_vdA3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_083 ())). Qed.
Lemma vdA3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40450 M) (st fx' R' 0x40454 M')
        /\ (forall x, In x KS_vdA3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = getr R (reg 10)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_084 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdB := BndP_Ns_114.LibSegNs_vdB.
Definition KS_vdB : list nat := Eval vm_compute in (BG.kept_list 60 PvdB.regs0 PvdB.regs_out0).
Lemma KS_vdB_ok : BG.kept_ok 60 PvdB.regs0 PvdB.regs_out0 KS_vdB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_085 ())). Qed.
Lemma vdB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (bv_unsigned (getr R (reg 10))) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40458 M) (st fx' R' 0x4045c M')
        /\ (forall x, In x KS_vdB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_086 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdCd := BndP_Ns_114.LibSegNs_vdCd.
Definition KS_vdCd : list nat := Eval vm_compute in (BG.kept_list 60 PvdCd.regs0 PvdCd.regs_out0).
Lemma KS_vdCd_ok : BG.kept_ok 60 PvdCd.regs0 PvdCd.regs_out0 KS_vdCd = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_087 ())). Qed.
Lemma vdCd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40464 M) (st fx' R' 0x4048c M')
        /\ (forall x, In x KS_vdCd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_088 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdCf := BndP_Ns_114.LibSegNs_vdCf.
Definition KS_vdCf : list nat := Eval vm_compute in (BG.kept_list 60 PvdCf.regs0 PvdCf.regs_out0).
Lemma KS_vdCf_ok : BG.kept_ok 60 PvdCf.regs0 PvdCf.regs_out0 KS_vdCf = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_089 ())). Qed.
Lemma vdCf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 1 -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 42) <= bv_unsigned a < ((V 2%nat) - 42) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 42) <= i < ((V 2%nat) - 42) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40464 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vdCf -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 263292
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 10%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 42)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_090 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdDd := BndP_Ns_114.LibSegNs_vdDd.
Definition KS_vdDd : list nat := Eval vm_compute in (BG.kept_list 60 PvdDd.regs0 PvdDd.regs_out0).
Lemma KS_vdDd_ok : BG.kept_ok 60 PvdDd.regs0 PvdDd.regs_out0 KS_vdDd = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_091 ())). Qed.
Lemma vdDd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (V 36%nat) <= 140737488355280 -> aligned (V 36%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40490 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vdDd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 263328
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_092 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdWf := BndP_Ns_114.LibSegNs_vdWf.
Definition KS_vdWf : list nat := Eval vm_compute in (BG.kept_list 60 PvdWf.regs0 PvdWf.regs_out0).
Lemma KS_vdWf_ok : BG.kept_ok 60 PvdWf.regs0 PvdWf.regs_out0 KS_vdWf = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_093 ())). Qed.
Lemma vdWf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 36%nat) <= 140737488355280 ->
  aligned (V 36%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40480 M) (st fx' R' 0x42198 M')
        /\ (forall x, In x KS_vdWf -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 263304
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_094 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdWd := BndP_Ns_114.LibSegNs_vdWd.
Definition KS_vdWd : list nat := Eval vm_compute in (BG.kept_list 60 PvdWd.regs0 PvdWd.regs_out0).
Lemma KS_vdWd_ok : BG.kept_ok 60 PvdWd.regs0 PvdWd.regs_out0 KS_vdWd = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_095 ())). Qed.
Lemma vdWd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 36%nat) <= 140737488355280 ->
  aligned (V 36%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x404a4 M) (st fx' R' 0x42220 M')
        /\ (forall x, In x KS_vdWd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 263340
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_096 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdJf := BndP_Ns_114.LibSegNs_vdJf.
Definition KS_vdJf : list nat := Eval vm_compute in (BG.kept_list 60 PvdJf.regs0 PvdJf.regs_out0).
Lemma KS_vdJf_ok : BG.kept_ok 60 PvdJf.regs0 PvdJf.regs_out0 KS_vdJf = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_097 ())). Qed.
Lemma vdJf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40488 M) (st fx' R' 0x404ac M')
        /\ (forall x, In x KS_vdJf -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_098 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdE0 := BndP_Ns_114.LibSegNs_vdE0.
Definition KS_vdE0 : list nat := Eval vm_compute in (BG.kept_list 60 PvdE0.regs0 PvdE0.regs_out0).
Lemma KS_vdE0_ok : BG.kept_ok 60 PvdE0.regs0 PvdE0.regs_out0 KS_vdE0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_099 ())). Qed.
Lemma vdE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) ->
  0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x404ac M) (st fx' R' 0x404d4 M')
        /\ (forall x, In x KS_vdE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_100 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdE1 := BndP_Ns_114.LibSegNs_vdE1.
Definition KS_vdE1 : list nat := Eval vm_compute in (BG.kept_list 60 PvdE1.regs0 PvdE1.regs_out0).
Lemma KS_vdE1_ok : BG.kept_ok 60 PvdE1.regs0 PvdE1.regs_out0 KS_vdE1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_101 ())). Qed.
Lemma vdE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) ->
  0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x404ac M) (st fx' R' 0x404d4 M')
        /\ (forall x, In x KS_vdE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_102 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdE1w := BndP_Ns_114.LibSegNs_vdE1w.
Definition KS_vdE1w : list nat := Eval vm_compute in (BG.kept_list 60 PvdE1w.regs0 PvdE1w.regs_out0).
Lemma KS_vdE1w_ok : BG.kept_ok 60 PvdE1w.regs0 PvdE1w.regs_out0 KS_vdE1w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_103 ())). Qed.
Lemma vdE1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x404ac M) (st fx' R' 0x404d4 M')
        /\ (forall x, In x KS_vdE1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_104 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvdZ := BndP_Ns_114.LibSegNs_vdZ.
Definition KS_vdZ : list nat := Eval vm_compute in (BG.kept_list 60 PvdZ.regs0 PvdZ.regs_out0).
Lemma KS_vdZ_ok : BG.kept_ok 60 PvdZ.regs0 PvdZ.regs_out0 KS_vdZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_105 ())). Qed.
Lemma vdZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x404dc M) (st fx' R' 0x404e0 M')
        /\ (forall x, In x KS_vdZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDblP ()) [] (Mh_0185_blobs1.kr_b_106 ())). Qed.
(* [comment removed for export] *)

End PNSENCDP.

End PnSEncDblP.
From Stdlib Require ZArith List Lia Bool Permutation FunctionalExtensionality. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034.
Module PnSEncDbl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146.PnEncCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088.PnFPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSEncDblP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_3fce0_41034.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncDbl () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK8cells_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib5Lists7ListDef6Forall00C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK9cred_sinkC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4kctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD5CREDsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD2rqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6or_indI47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3CSLC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD8st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD3COKC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC45stdpp9bitvector;definitions9bv_signedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX7fld_runC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP8vdZ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6step_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncDblP8PNSENCDP6KS_vdZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_4048cC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C49OSSVerify5KrLibDNs0_code_3fce0_410347F_4048cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_4048cC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40490C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40490C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40490C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40498C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40498C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40498C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_dblC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5pre_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pot_encC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncDbl7PNSENCD4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout9ne_doubleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS=v_double_specC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSENCD.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable AQ : pq_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis PO : NESK.sink_policy_ok P.
Hypothesis HBS : NESK.sp_hb P NESK.SMZ.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
(* [comment removed for export] *)
Hypothesis PB : NESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P.
Hypothesis NTBF32 : NECK.ntbf_spec RSEGS CAD L HI P 4 (ne_ntb_f32 EE).
Hypothesis NTBF64 : NECK.ntbf_spec RSEGS CAD L HI P 8 (ne_ntb_f64 EE).

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).
Abbreviation ec_state := (NEM.ec_state RSEGS CAD).

Section Call.
Hypothesis SPM : NESK.sp_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat : Z).
Variables (en : enc) (k : NESK.sink) (b e : bool) (ea : NECS.eargs).
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 4.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis Hov1 : sp <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : ov mod 8 = 0.
Hypothesis Hosk1 : sp <= osk.
Hypothesis Hosk2 : osk + 24 <= hl_sptop L.
Hypothesis Hosk3 : osk mod 8 = 0.
Hypothesis Hoec1 : sp <= oec.
Hypothesis Hoec2 : oec + 16 <= hl_sptop L.
Hypothesis Hoec3 : oec mod 8 = 0.
Hypothesis SEP1 : oec + 16 <= ov.
Hypothesis SEP2 : ov + 56 <= osk.
Hypothesis EA : enc_at M ov osk en.
Hypothesis SKA : sink_atP M osk k.
Hypothesis ECS : ec_state M oec b cat.
Hypothesis BASE : PMST.base_ok RSEGS CAD M.
Hypothesis ERR : PQST.err_ok RSEGS CAD AQ M e.
Hypothesis PRE : NESK.sk_z k + 9 <= NESK.SMZ.
Hypothesis CRED : PMSP.credit_le (NECS.pot_enc L P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
                         (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_atP M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS CAD M' -> PQST.err_ok RSEGS CAD AQ M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> NECS.step_w 9 ea en k b en' k' b' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 4) (NECS.W_enc CAD ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (NECS.pot_enc L P en k) (NECS.pot_enc L P en' k') ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Let cells : list (Z * Z) := [(sp - 8, bv_unsigned (getr R (PMK.reg 1))); (sp - 16, bv_unsigned (getr R (PMK.reg 8))); (sp - 24, bv_unsigned (getr R (PMK.reg 9)))].
Let CINV := (NECK.cinv L HI P M model LBX cr sp ov osk en k 20480 cells).
Lemma COK : NECK.cells_ok sp 48 cells.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_107 ())). Qed.
Lemma CREDs : PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_108 ())). Qed.
Lemma CXok : NECK.kctx L HI P R M model K LBX cr sp r ov osk en k 4 20480 48.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_109 ())). Qed.
Let Kfacts := NECK.facts_ok L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kfin := NECK.fin_facts AQ L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok oec cat b e.
Let Kcred := NECK.fin_credit L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kstart := NECK.cinv_start L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kframe := NECK.cinv_frame L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kencw := NECK.cinv_encwrite L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kpb := NECK.call_pb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK PB.
Let Kf32 := NECK.call_ntbf L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 4 (ne_ntb_f32 EE) NTBF32.
Let Kf64 := NECK.call_ntbf L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 8 (ne_ntb_f64 EE) NTBF64.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rq (Ri : bvmap 5 word) : Prop := getr Ri (PMK.reg 2) = Z_to_bv 64 (sp - 48) /\ getr Ri (PMK.reg 8) = Z_to_bv 64 ov /\ csl Ri.
Lemma rq_call Ra Rb : regs_preserved Ra Rb -> rq Ra -> rq Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_110 ())). Qed.
Lemma rq_piece (KS : list nat) Ra Rb : (forall x, In x KS -> getr Rb (PMK.reg x) = getr Ra (PMK.reg x)) ->
  forallb (fun k => existsb (Nat.eqb k) KS) (2 :: 8 :: CSL)%nat = true -> rq Ra -> rq Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_111 ())). Qed.
Lemma r_call Ra Rb (i : nat) vv : regs_preserved Ra Rb -> In i PMK.cs_all -> getr Ra (PMK.reg i) = vv -> getr Rb (PMK.reg i) = vv.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_112 ())). Qed.

(* [comment removed for export] *)
Lemma st_facts Mq mdq crq kq lo hi : CINV Mq mdq crq kq lo hi ->
  L5.writable RSEGS Mq (sp - 20480) 20480 /\ L5.writable RSEGS Mq ov 56 /\ L5.u64_at RSEGS Mq (ov + 8) osk
  /\ PMSP.model_ok mdq /\ hi_heap HI (NECS.eown en kq ++ LBX) crq Mq (m_vmmaps mdq) /\ L5C.stk (hl_sptop L) Mq sp 20480.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_113 ())). Qed.

Local Ltac bvr Rq := pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 8))) as RB8q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 9))) as RB9q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 10))) as RB10q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 11))) as RB11q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 12))) as RB12q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 18))) as RB18q;
  change (bv_modulus 64) with (2 ^ 64) in RB8q, RB9q, RB10q, RB11q, RB12q, RB18q.

(* [comment removed for export] *)
Lemma mid_piece (pc pc' c : Z) (fxq fx3 : FPState) Rq R3 Mq M3 mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> sp - 48 <= c -> c + 1 <= sp - 24 ->
  mem_grows Mq M3 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (c <= i < c + 1) -> M3 (Z_to_bv 64 i) = Mq (Z_to_bv 64 i)) ->
  msteps RSEGS (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) ->
  (CINV M3 mdq crq kq lo hi -> srealizes RSEGS SCFG (mkCfg (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) mdq) K) ->
  srealizes RSEGS SCFG (mkCfg (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_114 ())). Qed.
(* [comment removed for export] *)
Lemma ro_piece (pc pc' : Z) (fxq fx3 : FPState) Rq R3 Mq M3 mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> (forall a : word, M3 a = Mq a) ->
  msteps RSEGS (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) ->
  (CINV Mq mdq crq kq lo hi -> srealizes RSEGS SCFG (mkCfg (@mkst fx3 R3 (Z_to_bv 64 pc') Mq (seg_rom RSEGS)) mdq) K) ->
  srealizes RSEGS SCFG (mkCfg (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_115 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx7 : FPState) R7 M7 mdq crq kq lo hi :
  CINV M7 mdq crq kq lo hi -> 0 <= lo -> hi <= 9 ->
  getr R7 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1))) -> getr R7 (PMK.reg 2) = Z_to_bv 64 (sp - 48) ->
  getr R7 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R7 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) -> csl R7 ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 0x404d4 M7 mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_116 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ev_tail (fxq : FPState) Rq Mq mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> 0 <= lo -> hi <= 9 -> rq Rq -> getr Rq (PMK.reg 9) = Z_to_bv 64 (ov + 8) ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x404ac Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_117 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x40438 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_118 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem v_double_ok : NECS.v_double_spec RSEGS CAD AQ EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncDbl ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_119 ())). Qed.
End WithHeap.
End PNSENCD.

End PnSEncDbl.
Module PnSEncEndP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0159.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncEndP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEAaC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAa3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;KS_enEAa_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEAcC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAc3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;KS_enEAc_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEArC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEAr3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;KS_enEAr_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEAp1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP<KS_enEAp1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEAp2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP<KS_enEAp2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEAp26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:KS_enEAp2wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP=KS_enEAp2w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEAp2w6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEOaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOa3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;KS_enEOa_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEOcC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOc3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;KS_enEOc_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8KS_enEOrC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP6PenEOr3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP;KS_enEOr_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEOp1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP<KS_enEOp1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP9KS_enEOp2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP<KS_enEOp2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP7PenEOp26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP:KS_enEOp2wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP=KS_enEOp2w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncEndP7PNSENEP8PenEOp2w6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSENEP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_120 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_121 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_122 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_123 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_124 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_125 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_126 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_127 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_128 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_129 ())). Qed.
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
Module PenEAa := BndP_Ns_044.LibSegNs_enEAa.
Definition KS_enEAa : list nat := Eval vm_compute in (BG.kept_list 60 PenEAa.regs0 PenEAa.regs_out0).
Lemma KS_enEAa_ok : BG.kept_ok 60 PenEAa.regs0 PenEAa.regs_out0 KS_enEAa = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_130 ())). Qed.
Lemma enEAa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 4096 -> L5.u32_at RSEGS M ((V 39%nat) - 24) (V 37%nat) ->
  0 <= (V 37%nat) <= 4294967295 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 43%nat) -> 0 <= (V 43%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) ->
  0 <= (V 42%nat) <= 18446744073709551615 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 39%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ff0c M) (st fx' R' 0x3ff40 M')
        /\ (forall x, In x KS_enEAa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 42%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_131 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEAc := BndP_Ns_044.LibSegNs_enEAc.
Definition KS_enEAc : list nat := Eval vm_compute in (BG.kept_list 60 PenEAc.regs0 PenEAc.regs_out0).
Lemma KS_enEAc_ok : BG.kept_ok 60 PenEAc.regs0 PenEAc.regs_out0 KS_enEAc = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_132 ())). Qed.
Lemma enEAc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> 6 <= (bv_unsigned (getr R (reg 11))) <= 7 -> 140735332483072 <= (bv_unsigned (getr R (reg 12))) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ff5c M) (st fx' R' 0x41a54 M')
        /\ (forall x, In x KS_enEAc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 261988
        /\ getr R' (reg 10) = getr R (reg 12)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_133 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEAr := BndP_Ns_044.LibSegNs_enEAr.
Definition KS_enEAr : list nat := Eval vm_compute in (BG.kept_list 60 PenEAr.regs0 PenEAr.regs_out0).
Lemma KS_enEAr_ok : BG.kept_ok 60 PenEAr.regs0 PenEAr.regs_out0 KS_enEAr = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_134 ())). Qed.
Lemma enEAr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ff64 M) (st fx' R' 0x3ff78 M')
        /\ (forall x, In x KS_enEAr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_135 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEAp1 := BndP_Ns_044.LibSegNs_enEAp1.
Definition KS_enEAp1 : list nat := Eval vm_compute in (BG.kept_list 60 PenEAp1.regs0 PenEAp1.regs_out0).
Lemma KS_enEAp1_ok : BG.kept_ok 60 PenEAp1.regs0 PenEAp1.regs_out0 KS_enEAp1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_136 ())). Qed.
Lemma enEAp1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 ((V 38%nat) + 24) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> 4096 <= (V 38%nat) <= 140737488355304 ->
  aligned (V 38%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ff7c M) (st fx' R' 0x3ff78 M')
        /\ (forall x, In x KS_enEAp1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_137 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEAp2 := BndP_Ns_044.LibSegNs_enEAp2.
Definition KS_enEAp2 : list nat := Eval vm_compute in (BG.kept_list 60 PenEAp2.regs0 PenEAp2.regs_out0).
Lemma KS_enEAp2_ok : BG.kept_ok 60 PenEAp2.regs0 PenEAp2.regs_out0 KS_enEAp2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_138 ())). Qed.
Lemma enEAp2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> 4096 <= (V 38%nat) <= 140737488355328 ->
  4144 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 48 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 48) 48 ->
  (((V 39%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 48)) -> (((V 39%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 39%nat) - 48)) -> L5.u64_at RSEGS M ((V 39%nat) - 32) (V 47%nat) -> 0 <= (V 47%nat) <= 18446744073709551614 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= bv_unsigned a < ((V 39%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= i < ((V 39%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ff7c M) (st fx' R' 0x3ff78 M')
        /\ (forall x, In x KS_enEAp2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 32) ((V 47%nat) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 39%nat) - 24)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_139 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEAp2w := BndP_Ns_044.LibSegNs_enEAp2w.
Definition KS_enEAp2w : list nat := Eval vm_compute in (BG.kept_list 60 PenEAp2w.regs0 PenEAp2w.regs_out0).
Lemma KS_enEAp2w_ok : BG.kept_ok 60 PenEAp2w.regs0 PenEAp2w.regs_out0 KS_enEAp2w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_140 ())). Qed.
Lemma enEAp2w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> 4096 <= (V 38%nat) <= 140737488355328 ->
  4144 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 48 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 48) 48 ->
  (((V 39%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 48)) -> (((V 39%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 39%nat) - 48)) -> L5.u64_at RSEGS M ((V 39%nat) - 32) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= bv_unsigned a < ((V 39%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= i < ((V 39%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ff7c M) (st fx' R' 0x3ff78 M')
        /\ (forall x, In x KS_enEAp2w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 39%nat) - 24)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_141 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEOa := BndP_Ns_044.LibSegNs_enEOa.
Definition KS_enEOa : list nat := Eval vm_compute in (BG.kept_list 60 PenEOa.regs0 PenEOa.regs_out0).
Lemma KS_enEOa_ok : BG.kept_ok 60 PenEOa.regs0 PenEOa.regs_out0 KS_enEOa = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_142 ())). Qed.
Lemma enEOa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.u32_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 48) (V 36%nat) -> 1 <= (V 36%nat) <= 4096 -> L5.u32_at RSEGS M ((V 39%nat) - 24) (V 37%nat) ->
  0 <= (V 37%nat) <= 4294967295 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 43%nat) -> 0 <= (V 43%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) ->
  0 <= (V 42%nat) <= 18446744073709551615 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 39%nat) - 24)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> ~ (((bv_unsigned (getr R (reg 10))) + 48) <= i < ((bv_unsigned (getr R (reg 10))) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x406e8 M) (st fx' R' 0x4071c M')
        /\ (forall x, In x KS_enEOa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 42%nat)
        /\ L5.u32_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 48) ((V 36%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_143 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEOc := BndP_Ns_044.LibSegNs_enEOc.
Definition KS_enEOc : list nat := Eval vm_compute in (BG.kept_list 60 PenEOc.regs0 PenEOc.regs_out0).
Lemma KS_enEOc_ok : BG.kept_ok 60 PenEOc.regs0 PenEOc.regs_out0 KS_enEOc = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_144 ())). Qed.
Lemma enEOc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> 6 <= (bv_unsigned (getr R (reg 11))) <= 7 -> 140735332483072 <= (bv_unsigned (getr R (reg 12))) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40738 M) (st fx' R' 0x41a54 M')
        /\ (forall x, In x KS_enEOc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 264000
        /\ getr R' (reg 10) = getr R (reg 12)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_145 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEOr := BndP_Ns_045.LibSegNs_enEOr.
Definition KS_enEOr : list nat := Eval vm_compute in (BG.kept_list 60 PenEOr.regs0 PenEOr.regs_out0).
Lemma KS_enEOr_ok : BG.kept_ok 60 PenEOr.regs0 PenEOr.regs_out0 KS_enEOr = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_146 ())). Qed.
Lemma enEOr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40740 M) (st fx' R' 0x40754 M')
        /\ (forall x, In x KS_enEOr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_147 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEOp1 := BndP_Ns_045.LibSegNs_enEOp1.
Definition KS_enEOp1 : list nat := Eval vm_compute in (BG.kept_list 60 PenEOp1.regs0 PenEOp1.regs_out0).
Lemma KS_enEOp1_ok : BG.kept_ok 60 PenEOp1.regs0 PenEOp1.regs_out0 KS_enEOp1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_148 ())). Qed.
Lemma enEOp1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 ((V 38%nat) + 24) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> 4096 <= (V 38%nat) <= 140737488355304 ->
  aligned (V 38%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40758 M) (st fx' R' 0x40754 M')
        /\ (forall x, In x KS_enEOp1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) (V 38%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_149 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEOp2 := BndP_Ns_045.LibSegNs_enEOp2.
Definition KS_enEOp2 : list nat := Eval vm_compute in (BG.kept_list 60 PenEOp2.regs0 PenEOp2.regs_out0).
Lemma KS_enEOp2_ok : BG.kept_ok 60 PenEOp2.regs0 PenEOp2.regs_out0 KS_enEOp2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_150 ())). Qed.
Lemma enEOp2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> 4096 <= (V 38%nat) <= 140737488355328 ->
  4144 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 48 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 48) 48 ->
  (((V 39%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 48)) -> (((V 39%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 39%nat) - 48)) -> L5.u64_at RSEGS M ((V 39%nat) - 32) (V 47%nat) -> 0 <= (V 47%nat) <= 18446744073709551614 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= bv_unsigned a < ((V 39%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= i < ((V 39%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40758 M) (st fx' R' 0x40754 M')
        /\ (forall x, In x KS_enEOp2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 32) ((V 47%nat) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 39%nat) - 24)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_151 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PenEOp2w := BndP_Ns_045.LibSegNs_enEOp2w.
Definition KS_enEOp2w : list nat := Eval vm_compute in (BG.kept_list 60 PenEOp2w.regs0 PenEOp2w.regs_out0).
Lemma KS_enEOp2w_ok : BG.kept_ok 60 PenEOp2w.regs0 PenEOp2w.regs_out0 KS_enEOp2w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_152 ())). Qed.
Lemma enEOp2w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> 4096 <= (V 38%nat) <= 140737488355328 ->
  4144 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 48 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 48) 48 ->
  (((V 39%nat) - 48) + 48 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 48)) -> (((V 39%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 39%nat) - 48)) -> L5.u64_at RSEGS M ((V 39%nat) - 32) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 32) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= bv_unsigned a < ((V 39%nat) - 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 32) <= i < ((bv_unsigned (getr R (reg 10))) + 32) + 8) -> ~ (((V 39%nat) - 32) <= i < ((V 39%nat) - 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40758 M) (st fx' R' 0x40754 M')
        /\ (forall x, In x KS_enEOp2w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 32) ((V 39%nat) - 24)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEndP ()) [] (Mh_0185_blobs1.kr_b_153 ())). Qed.
(* [comment removed for export] *)

End PNSENEP.

End PnSEncEndP.
Module PnSEncEnd.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088.PnFPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSEncEndP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_3fce0_41034.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncEnd () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions9bv_signedK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_sltiuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_srlC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK4npc4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_sltiuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_srlC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX@regupd_other_idxC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqI47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExec<step_bgeu_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK4npcKC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib7Mh_00889PnFPSteps4PEFX?regupd_same_idxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExec<step_bgeu_tkC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula07C49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06K4ELinuxProcessSemantics5Riscv5Instr5aluop01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK7cmp_runC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3fef8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3fefcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3ff00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3ff04C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3ff08C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3ff0cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_3ff10C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3fef8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3fef8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3fefcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3fefcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3ff00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3ff00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3ff04C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3ff04C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3ff08C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3ff08C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3ff0cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3ff0cC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_3ff10C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_3ff10C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406d4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406d8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406dcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406e0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406e4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406e8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_406ecC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406d4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406d4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406d8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406d8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406dcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406dcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406e0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406e0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406e4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406e4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406e8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406e8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_406ecC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_406ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses6eq_iffC69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG8rdn_someC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib?AxSymExec3Sound4AX2SCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesI47Corelib4Init5Peano2le00C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXKword_to_le_bytes_of_bytes_nC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00189NemLayout8ne_addrs00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface;heap_layout00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7enc_endC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eend00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:pot_estackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pot_encC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK;sink_policy00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5err_WC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK7pot_endC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEK8eown_endC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eend01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eend02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_endC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_endC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_endC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEA4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout:ne_end_arrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS>v_end_arr_specC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncEnd7PNSENEO4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout:ne_end_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS>v_end_obj_specC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PNSENEK.
Import PMS.
Import NEM.
Section K.
Context {bmK : BMode}.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma npc4 (pc : Z) : 0 <= pc -> pc + 4 < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) 4 = Z_to_bv 64 (pc + 4).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_154 ())). Qed.
Lemma npcK (pc k : Z) : 0 <= pc -> 0 <= pc + k -> pc + k < 2 ^ 64 -> pc < 2 ^ 64 -> v_addi (Z_to_bv 64 pc) k = Z_to_bv 64 (pc + k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_155 ())). Qed.

(* [comment removed for export] *)
Lemma cmp_run (fx : FPState) R M (pc : Z) (W0 W1 W2 W3 W4 W5 W6 : bv 32) (i2 i5 : bv 13) (i4 : bv 21) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W0 -> is_ecall W0 = false -> decode_any W0 = Some (OpImm ALU_SLTU 15 15 1, 4%Z) ->
  fetch_word RSEGS (Z_to_bv 64 (pc + 4)) = Some W1 -> is_ecall W1 = false -> decode_any W1 = Some (Op ALU_SRL 15 16 15, 4%Z) ->
  fetch_word RSEGS (Z_to_bv 64 (pc + 8)) = Some W2 -> is_ecall W2 = false -> decode_any W2 = Some (Branch BC_GEU 15 14 i2, 4%Z) -> bv_signed i2 = 12 ->
  fetch_word RSEGS (Z_to_bv 64 (pc + 12)) = Some W3 -> is_ecall W3 = false -> decode_any W3 = Some (OpImm ALU_ADD 11 0 7, 4%Z) ->
  fetch_word RSEGS (Z_to_bv 64 (pc + 16)) = Some W4 -> is_ecall W4 = false -> decode_any W4 = Some (Jal 0 i4, 4%Z) -> bv_signed i4 = 12 ->
  fetch_word RSEGS (Z_to_bv 64 (pc + 20)) = Some W5 -> is_ecall W5 = false -> decode_any W5 = Some (Branch BC_GEU 14 15 i5, 4%Z) -> bv_signed i5 = 40 ->
  fetch_word RSEGS (Z_to_bv 64 (pc + 24)) = Some W6 -> is_ecall W6 = false -> decode_any W6 = Some (OpImm ALU_ADD 11 0 6, 4%Z) ->
  0 <= pc -> pc + 64 < 2 ^ 64 ->
  exists R', (forall x : nat, (x < 32)%nat -> x <> 11%nat -> x <> 15%nat -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x)))
    /\ ( (msteps RSEGS (st fx R pc M) (st fx R' (pc + 28) M) /\ (getr R' 11%bv = Z_to_bv 64 7 \/ getr R' 11%bv = Z_to_bv 64 6))
         \/ (msteps RSEGS (st fx R pc M) (st fx R' (pc + 60) M) /\ getr R' 11%bv = getr R 11%bv) ).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_156 ())). Qed.
Lemma cmp_run_EA fx R M : exists R', (forall x : nat, (x < 32)%nat -> x <> 11%nat -> x <> 15%nat -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x)))
    /\ ( (msteps RSEGS (st fx R 0x3ff40 M) (st fx R' 0x3ff5c M) /\ (getr R' 11%bv = Z_to_bv 64 7 \/ getr R' 11%bv = Z_to_bv 64 6))
         \/ (msteps RSEGS (st fx R 0x3ff40 M) (st fx R' 0x3ff7c M) /\ getr R' 11%bv = getr R 11%bv) ).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_157 ())). Qed.
Lemma cmp_run_EO fx R M : exists R', (forall x : nat, (x < 32)%nat -> x <> 11%nat -> x <> 15%nat -> getr R' (Z_to_bv 5 (Z.of_nat x)) = getr R (Z_to_bv 5 (Z.of_nat x)))
    /\ ( (msteps RSEGS (st fx R 0x4071c M) (st fx R' 0x40738 M) /\ (getr R' 11%bv = Z_to_bv 64 7 \/ getr R' 11%bv = Z_to_bv 64 6))
         \/ (msteps RSEGS (st fx R 0x4071c M) (st fx R' 0x40758 M) /\ getr R' 11%bv = getr R 11%bv) ).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_158 ())). Qed.

(* [comment removed for export] *)
Lemma u32_of_defined (M : word -> option byte) a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4 ->
  exists w, 0 <= w < 2 ^ 32 /\ L5.u32_at RSEGS M a w.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_159 ())). Qed.

(* [comment removed for export] *)
Lemma enc_at_upd (E : ne_addrs) (L : heap_layout) (M M' : word -> option byte) ov osk en n' d' :
  NEM.enc_at RSEGS E L PMSP.T3 PMSP.T4 M ov osk en -> mem_grows M M' -> 0 <= ov -> ov + 56 <= 2 ^ 64 ->
  L5C.agree_on M M' ov 32 -> L5C.agree_on M M' (ov + 40) 8 ->
  L5.u64_at RSEGS M' (ov + 32) (en_b en + ESZ * n') -> L5.u32_at RSEGS M' (ov + 48) d' ->
  0 <= d' <= n' -> n' <= en_n en ->
  NEM.enc_at RSEGS E L PMSP.T3 PMSP.T4 M' ov osk (ENC (en_b en) (en_k en) n' d').
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_160 ())). Qed.

(* [comment removed for export] *)
Lemma eown_end en o k : NECS.eown (NECS.enc_end en o) k = NECS.eown en k.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_161 ())). Qed.
Lemma pot_end L P en o k : NECS.pot_enc L P (NECS.enc_end en o) k = NECS.pot_enc L P en k.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["K"] (Mh_0185_blobs1.kr_b_162 ())). Qed.
End K.
End PNSENEK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PNSENEA.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable AQ : pq_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
(* [comment removed for export] *)
Hypothesis MEC : PQR.make_ec_spec RSEGS CAD AQ L HI.

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).
Abbreviation ec_state := (NEM.ec_state RSEGS CAD).

Section Call.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat : Z).
Variables (en : enc) (k : NESK.sink) (b e : bool) (ea : NECS.eargs).
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 4.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 oec.
Hypothesis Hov1 : sp <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : ov mod 8 = 0.
Hypothesis Hosk1 : sp <= osk.
Hypothesis Hosk2 : osk + 24 <= hl_sptop L.
Hypothesis Hosk3 : osk mod 8 = 0.
Hypothesis Hoec1 : sp <= oec.
Hypothesis Hoec2 : oec + 16 <= hl_sptop L.
Hypothesis Hoec3 : oec mod 8 = 0.
Hypothesis SEP1 : oec + 16 <= ov.
Hypothesis SEP2 : ov + 56 <= osk.
Hypothesis EA : enc_at M ov osk en.
Hypothesis SKA : sink_atP M osk k.
Hypothesis ECS : ec_state M oec b cat.
Hypothesis BASE : PMST.base_ok RSEGS CAD M.
Hypothesis ERR : PQST.err_ok RSEGS CAD AQ M e.
Hypothesis PRE : 1 <= en_depth en.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
                         (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_atP M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS CAD M' -> PQST.err_ok RSEGS CAD AQ M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> NECS.step_end ea en k b en' k' b' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 4) (NECS.W_enc CAD ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (NECS.pot_enc L P en k) (NECS.pot_enc L P en' k') ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

Let LB : list (Z * Z) := NECS.eown en k ++ LBX.
(* [comment removed for export] *)
Let WALL : list L5.range := NECS.W_enc CAD ov osk oec.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

Lemma wall_enc a : ov + 24 <= a < ov + 56 -> PMK.inW WALL a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_163 ())). Qed.
Lemma wall_ec a : oec <= a < oec + 16 -> PMK.inW WALL a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_164 ())). Qed.
Lemma wall_err rr a : In rr (PMSP.err_W CAD) -> L5.in_rng rr a -> PMK.inW WALL a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_165 ())). Qed.

(* [comment removed for export] *)
Lemma fin (o : NECS.eend) (fx7 : FPState) R7 M7 (b' e' : bool) :
  regs_preserved R R7 ->
  enc_at M7 ov osk (NECS.enc_end en o) -> sink_atP M7 osk k -> ec_state M7 oec b' cat -> PMST.base_ok RSEGS CAD M7 -> PQST.err_ok RSEGS CAD AQ M7 e' ->
  (b = true -> b' = true) -> (e = true -> e' = true) -> (o = NECS.EPop -> b' = b) -> (o = NECS.EKeep -> b' = true) ->
  PMK.ek L LBX sp 20480 WALL M M7 -> PMK.dk L LBX sp 20480 M M7 -> L5C.stk (hl_sptop L) M7 sp 20480 ->
  hi_heap HI LB cr M7 (m_vmmaps model) ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 r M7 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_166 ())). Qed.

(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x3ff0c M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_167 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem v_end_arr_ok : NECS.v_end_arr_spec RSEGS CAD AQ EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_168 ())). Qed.
End WithHeap.
End PNSENEA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PNSENEO.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable AQ : pq_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
(* [comment removed for export] *)
Hypothesis MEC : PQR.make_ec_spec RSEGS CAD AQ L HI.

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).
Abbreviation ec_state := (NEM.ec_state RSEGS CAD).

Section Call.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat : Z).
Variables (en : enc) (k : NESK.sink) (b e : bool) (ea : NECS.eargs).
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 4.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 oec.
Hypothesis Hov1 : sp <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : ov mod 8 = 0.
Hypothesis Hosk1 : sp <= osk.
Hypothesis Hosk2 : osk + 24 <= hl_sptop L.
Hypothesis Hosk3 : osk mod 8 = 0.
Hypothesis Hoec1 : sp <= oec.
Hypothesis Hoec2 : oec + 16 <= hl_sptop L.
Hypothesis Hoec3 : oec mod 8 = 0.
Hypothesis SEP1 : oec + 16 <= ov.
Hypothesis SEP2 : ov + 56 <= osk.
Hypothesis EA : enc_at M ov osk en.
Hypothesis SKA : sink_atP M osk k.
Hypothesis ECS : ec_state M oec b cat.
Hypothesis BASE : PMST.base_ok RSEGS CAD M.
Hypothesis ERR : PQST.err_ok RSEGS CAD AQ M e.
Hypothesis PRE : 1 <= en_depth en.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
                         (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_atP M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS CAD M' -> PQST.err_ok RSEGS CAD AQ M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> NECS.step_end ea en k b en' k' b' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 4) (NECS.W_enc CAD ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (NECS.pot_enc L P en k) (NECS.pot_enc L P en' k') ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

Let LB : list (Z * Z) := NECS.eown en k ++ LBX.
(* [comment removed for export] *)
Let WALL : list L5.range := NECS.W_enc CAD ov osk oec.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

Lemma wall_enc a : ov + 24 <= a < ov + 56 -> PMK.inW WALL a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_169 ())). Qed.
Lemma wall_ec a : oec <= a < oec + 16 -> PMK.inW WALL a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_170 ())). Qed.
Lemma wall_err rr a : In rr (PMSP.err_W CAD) -> L5.in_rng rr a -> PMK.inW WALL a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_171 ())). Qed.

(* [comment removed for export] *)
Lemma fin (o : NECS.eend) (fx7 : FPState) R7 M7 (b' e' : bool) :
  regs_preserved R R7 ->
  enc_at M7 ov osk (NECS.enc_end en o) -> sink_atP M7 osk k -> ec_state M7 oec b' cat -> PMST.base_ok RSEGS CAD M7 -> PQST.err_ok RSEGS CAD AQ M7 e' ->
  (b = true -> b' = true) -> (e = true -> e' = true) -> (o = NECS.EPop -> b' = b) -> (o = NECS.EKeep -> b' = true) ->
  PMK.ek L LBX sp 20480 WALL M M7 -> PMK.dk L LBX sp 20480 M M7 -> L5C.stk (hl_sptop L) M7 sp 20480 ->
  hi_heap HI LB cr M7 (m_vmmaps model) ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 r M7 model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_172 ())). Qed.

(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x406e8 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_173 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem v_end_obj_ok : NECS.v_end_obj_spec RSEGS CAD AQ EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncEnd ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_174 ())). Qed.
End WithHeap.
End PNSENEO.

End PnSEncEnd.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165.
Module PnSEncU64P.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncU64P () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuA5C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA5<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA56cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA53kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA53ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuA5_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuA7C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA76cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA73ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuA7_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuA8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA86cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuA83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuA8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuA16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuA16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuA32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA326cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuA32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA649regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuA64C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA64<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA646cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA643kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuA643ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuA64_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuB8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuB83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuB8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuB16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuB16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuB32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuB32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB649regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuB64C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB64<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB643kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuB643ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuB64_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuJ5C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuJ53ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuJ5_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuJ16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuJ16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuJ32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuJ32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ649regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuJ64C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ64<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ643kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuJ643ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuJ64_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuE0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuE0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuE1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE13NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:KS_vuE1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P5PvuE16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuE1wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P;KS_vuE1w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P6PvuE1w6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSENU6P.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_175 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_176 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_177 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_178 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_179 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_180 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_181 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_182 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_183 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_184 ())). Qed.
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
Module PvuA5 := BndP_Ns_097.LibSegNs_vuA5.
Definition KS_vuA5 : list nat := Eval vm_compute in (BG.kept_list 60 PvuA5.regs0 PvuA5.regs_out0).
Lemma KS_vuA5_ok : BG.kept_ok 60 PvuA5.regs0 PvuA5.regs_out0 KS_vuA5 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_185 ())). Qed.
Lemma vuA5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 5 <= (bv_unsigned (getr R (reg 12))) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40010 M) (st fx' R' 0x41e18 M')
        /\ (forall x, In x KS_vuA5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262404
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_186 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuA7 := BndP_Ns_097.LibSegNs_vuA7.
Definition KS_vuA7 : list nat := Eval vm_compute in (BG.kept_list 60 PvuA7.regs0 PvuA7.regs_out0).
Lemma KS_vuA7_ok : BG.kept_ok 60 PvuA7.regs0 PvuA7.regs_out0 KS_vuA7 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_187 ())). Qed.
Lemma vuA7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 127 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40010 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vuA7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262460
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 38)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_188 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuA8 := BndP_Ns_097.LibSegNs_vuA8.
Definition KS_vuA8 : list nat := Eval vm_compute in (BG.kept_list 60 PvuA8.regs0 PvuA8.regs_out0).
Lemma KS_vuA8_ok : BG.kept_ok 60 PvuA8.regs0 PvuA8.regs_out0 KS_vuA8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_189 ())). Qed.
Lemma vuA8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 128 <= (bv_unsigned (getr R (reg 11))) <= 255 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40010 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vuA8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262444
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 37)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_190 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuA16 := BndP_Ns_097.LibSegNs_vuA16.
Definition KS_vuA16 : list nat := Eval vm_compute in (BG.kept_list 60 PvuA16.regs0 PvuA16.regs_out0).
Lemma KS_vuA16_ok : BG.kept_ok 60 PvuA16.regs0 PvuA16.regs_out0 KS_vuA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_191 ())). Qed.
Lemma vuA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 256 <= (bv_unsigned (getr R (reg 11))) <= 65535 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40010 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vuA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262536
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 35)
        /\ getr R' (reg 18) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_192 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuA32 := BndP_Ns_097.LibSegNs_vuA32.
Definition KS_vuA32 : list nat := Eval vm_compute in (BG.kept_list 60 PvuA32.regs0 PvuA32.regs_out0).
Lemma KS_vuA32_ok : BG.kept_ok 60 PvuA32.regs0 PvuA32.regs_out0 KS_vuA32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_193 ())). Qed.
Lemma vuA32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 65536 <= (bv_unsigned (getr R (reg 11))) <= 4294967295 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40010 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vuA32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262568
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 34)
        /\ getr R' (reg 18) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_194 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuA64 := BndP_Ns_097.LibSegNs_vuA64.
Definition KS_vuA64 : list nat := Eval vm_compute in (BG.kept_list 60 PvuA64.regs0 PvuA64.regs_out0).
Lemma KS_vuA64_ok : BG.kept_ok 60 PvuA64.regs0 PvuA64.regs_out0 KS_vuA64 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_195 ())). Qed.
Lemma vuA64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4294967296 <= (bv_unsigned (getr R (reg 11))) <= 18446744073709551615 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40010 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vuA64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262372
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 33)
        /\ getr R' (reg 18) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_196 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuB8 := BndP_Ns_098.LibSegNs_vuB8.
Definition KS_vuB8 : list nat := Eval vm_compute in (BG.kept_list 60 PvuB8.regs0 PvuB8.regs_out0).
Lemma KS_vuB8_ok : BG.kept_ok 60 PvuB8.regs0 PvuB8.regs_out0 KS_vuB8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_197 ())). Qed.
Lemma vuB8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 128 <= (V 11%nat) <= 255 -> 0 <= (V 12%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 36) <= bv_unsigned a < ((V 2%nat) - 36) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 36) <= i < ((V 2%nat) - 36) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4012c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_vuB8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262460
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 36)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_198 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuB16 := BndP_Ns_098.LibSegNs_vuB16.
Definition KS_vuB16 : list nat := Eval vm_compute in (BG.kept_list 60 PvuB16.regs0 PvuB16.regs_out0).
Lemma KS_vuB16_ok : BG.kept_ok 60 PvuB16.regs0 PvuB16.regs_out0 KS_vuB16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_199 ())). Qed.
Lemma vuB16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 36%nat) <= 140737488355280 ->
  aligned (V 36%nat) 8 -> 256 <= (V 11%nat) <= 65535 -> 0 <= (V 12%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40188 M) (st fx' R' 0x41aec M')
        /\ (forall x, In x KS_vuB16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262548
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_200 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuB32 := BndP_Ns_098.LibSegNs_vuB32.
Definition KS_vuB32 : list nat := Eval vm_compute in (BG.kept_list 60 PvuB32.regs0 PvuB32.regs_out0).
Lemma KS_vuB32_ok : BG.kept_ok 60 PvuB32.regs0 PvuB32.regs_out0 KS_vuB32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_201 ())). Qed.
Lemma vuB32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 36%nat) <= 140737488355280 ->
  aligned (V 36%nat) 8 -> 65536 <= (V 11%nat) <= 4294967295 -> 0 <= (V 12%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x401a8 M) (st fx' R' 0x41b50 M')
        /\ (forall x, In x KS_vuB32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262580
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_202 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuB64 := BndP_Ns_098.LibSegNs_vuB64.
Definition KS_vuB64 : list nat := Eval vm_compute in (BG.kept_list 60 PvuB64.regs0 PvuB64.regs_out0).
Lemma KS_vuB64_ok : BG.kept_ok 60 PvuB64.regs0 PvuB64.regs_out0 KS_vuB64 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_203 ())). Qed.
Lemma vuB64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 36%nat) <= 140737488355280 ->
  aligned (V 36%nat) 8 -> 4294967296 <= (V 11%nat) <= 18446744073709551615 -> 0 <= (V 12%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x400e4 M) (st fx' R' 0x41f34 M')
        /\ (forall x, In x KS_vuB64 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 262384
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_204 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuJ5 := BndP_Ns_098.LibSegNs_vuJ5.
Definition KS_vuJ5 : list nat := Eval vm_compute in (BG.kept_list 60 PvuJ5.regs0 PvuJ5.regs_out0).
Lemma KS_vuJ5_ok : BG.kept_ok 60 PvuJ5.regs0 PvuJ5.regs_out0 KS_vuJ5 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_205 ())). Qed.
Lemma vuJ5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40104 M) (st fx' R' 0x4013c M')
        /\ (forall x, In x KS_vuJ5 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_206 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuJ16 := BndP_Ns_098.LibSegNs_vuJ16.
Definition KS_vuJ16 : list nat := Eval vm_compute in (BG.kept_list 60 PvuJ16.regs0 PvuJ16.regs_out0).
Lemma KS_vuJ16_ok : BG.kept_ok 60 PvuJ16.regs0 PvuJ16.regs_out0 KS_vuJ16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_207 ())). Qed.
Lemma vuJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40194 M) (st fx' R' 0x4013c M')
        /\ (forall x, In x KS_vuJ16 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_208 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuJ32 := BndP_Ns_098.LibSegNs_vuJ32.
Definition KS_vuJ32 : list nat := Eval vm_compute in (BG.kept_list 60 PvuJ32.regs0 PvuJ32.regs_out0).
Lemma KS_vuJ32_ok : BG.kept_ok 60 PvuJ32.regs0 PvuJ32.regs_out0 KS_vuJ32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_209 ())). Qed.
Lemma vuJ32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x401b4 M) (st fx' R' 0x4013c M')
        /\ (forall x, In x KS_vuJ32 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_210 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuJ64 := BndP_Ns_098.LibSegNs_vuJ64.
Definition KS_vuJ64 : list nat := Eval vm_compute in (BG.kept_list 60 PvuJ64.regs0 PvuJ64.regs_out0).
Lemma KS_vuJ64_ok : BG.kept_ok 60 PvuJ64.regs0 PvuJ64.regs_out0 KS_vuJ64 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_211 ())). Qed.
Lemma vuJ64_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x400f0 M) (st fx' R' 0x4013c M')
        /\ (forall x, In x KS_vuJ64 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_212 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuE0 := BndP_Ns_098.LibSegNs_vuE0.
Definition KS_vuE0 : list nat := Eval vm_compute in (BG.kept_list 60 PvuE0.regs0 PvuE0.regs_out0).
Lemma KS_vuE0_ok : BG.kept_ok 60 PvuE0.regs0 PvuE0.regs_out0 KS_vuE0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_213 ())). Qed.
Lemma vuE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) ->
  0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4013c M) (st fx' R' 0x4016c M')
        /\ (forall x, In x KS_vuE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_214 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuE1 := BndP_Ns_098.LibSegNs_vuE1.
Definition KS_vuE1 : list nat := Eval vm_compute in (BG.kept_list 60 PvuE1.regs0 PvuE1.regs_out0).
Lemma KS_vuE1_ok : BG.kept_ok 60 PvuE1.regs0 PvuE1.regs_out0 KS_vuE1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_215 ())). Qed.
Lemma vuE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) ->
  0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4013c M) (st fx' R' 0x4016c M')
        /\ (forall x, In x KS_vuE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_216 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvuE1w := BndP_Ns_098.LibSegNs_vuE1w.
Definition KS_vuE1w : list nat := Eval vm_compute in (BG.kept_list 60 PvuE1w.regs0 PvuE1w.regs_out0).
Lemma KS_vuE1w_ok : BG.kept_ok 60 PvuE1w.regs0 PvuE1w.regs_out0 KS_vuE1w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_217 ())). Qed.
Lemma vuE1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4013c M) (st fx' R' 0x4016c M')
        /\ (forall x, In x KS_vuE1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64P ()) [] (Mh_0185_blobs1.kr_b_218 ())). Qed.
(* [comment removed for export] *)

End PNSENU6P.

End PnSEncU64P.
Module PnSEncU64.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146.PnEncCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSEncU64P OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_3fce0_41034.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncU64 () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z8leb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic2or00c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU642wbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib5Lists7ListDef6Forall02I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1N02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK8cells_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK9cred_sinkC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4kctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU645CREDsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU642rqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU643cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indI47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU643CSLC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU648st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU643COKC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusI47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuJ64_concC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P9vuJ5_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuJ16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P:vuJ32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU647ev_tailC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU648ro_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuJ64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P7KS_vuJ5C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuJ16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncU64P8PNSENU6P8KS_vuJ32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pot_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_tagC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncU648PNSENU644mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout9ne_uint64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS=v_uint64_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_NONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_ESECC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01". Local Ltac lia := L5FastLia.plia.

Module PNSENU64.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable AQ : pq_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis PO : NESK.sink_policy_ok P.
Hypothesis HBS : NESK.sp_hb P NESK.SMZ.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
(* [comment removed for export] *)
Hypothesis PB : NESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P.
Hypothesis NTB16 : NECS.ntb_spec RSEGS CAD L HI P 2 (ne_ntb_u16 EE).
Hypothesis NTB32 : NECS.ntb_spec RSEGS CAD L HI P 4 (ne_ntb_u32 EE).
Hypothesis NTB64 : NECS.ntb_spec RSEGS CAD L HI P 8 (ne_ntb_u64 EE).
Hypothesis WTS : NECS.write_timestamp_spec RSEGS CAD EE L HI P.

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).
Abbreviation ec_state := (NEM.ec_state RSEGS CAD).

(* [comment removed for export] *)
Definition wb (tg v : Z) : Z := if tg =? TAG_ESEC then 15 else w_u64 v.
Lemma wbound tg v hi :
  (tg = 5 /\ hi <= 15) \/ (tg = 0 /\ (hi <= 1 \/ (hi <= 2 /\ 127 < v) \/ (hi <= 3 /\ 255 < v) \/ (hi <= 5 /\ 65535 < v) \/ (hi <= 9 /\ 4294967295 < v))) ->
  hi <= wb tg v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_219 ())). Qed.

Section Call.
Hypothesis SPM : NESK.sp_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat v tag : Z).
Variables (en : enc) (k : NESK.sink) (b e : bool) (ea : NECS.eargs).
Hypothesis EAV : NECS.ea_val ea = v.
Hypothesis EAT : NECS.ea_tag ea = tag.
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 4.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 v.
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 tag.
Hypothesis Hv : 0 <= v < 2 ^ 64.
Hypothesis Htag : tag = 0 \/ tag = 5.
Hypothesis Hov1 : sp <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : ov mod 8 = 0.
Hypothesis Hosk1 : sp <= osk.
Hypothesis Hosk2 : osk + 24 <= hl_sptop L.
Hypothesis Hosk3 : osk mod 8 = 0.
Hypothesis Hoec1 : sp <= oec.
Hypothesis Hoec2 : oec + 16 <= hl_sptop L.
Hypothesis Hoec3 : oec mod 8 = 0.
Hypothesis SEP1 : oec + 16 <= ov.
Hypothesis SEP2 : ov + 56 <= osk.
Hypothesis EA : enc_at M ov osk en.
Hypothesis SKA : sink_atP M osk k.
Hypothesis ECS : ec_state M oec b cat.
Hypothesis BASE : PMST.base_ok RSEGS CAD M.
Hypothesis ERR : PQST.err_ok RSEGS CAD AQ M e.
Hypothesis PRE : NESK.sk_z k + wb tag v <= NESK.SMZ.   (* [comment removed for export] *)
Hypothesis CRED : PMSP.credit_le (NECS.pot_enc L P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
                         (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_atP M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS CAD M' -> PQST.err_ok RSEGS CAD AQ M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> NECS.step_u64 ea en k b en' k' b' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 4) (NECS.W_enc CAD ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (NECS.pot_enc L P en k) (NECS.pot_enc L P en' k') ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Let cells : list (Z * Z) := [(sp - 8, bv_unsigned (getr R (PMK.reg 1))); (sp - 16, bv_unsigned (getr R (PMK.reg 8))); (sp - 24, bv_unsigned (getr R (PMK.reg 9)));
                             (sp - 32, bv_unsigned (getr R (PMK.reg 18)))].
Let CINV := (NECK.cinv L HI P M model LBX cr sp ov osk en k 20480 cells).
Lemma COK : NECK.cells_ok sp 48 cells.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_220 ())). Qed.
Lemma CREDs : PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_221 ())). Qed.
Lemma CXok : NECK.kctx L HI P R M model K LBX cr sp r ov osk en k 4 20480 48.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_222 ())). Qed.
Let Kfacts := NECK.facts_ok L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kfin := NECK.fin_facts AQ L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok oec cat b e.
Let Kcred := NECK.fin_credit L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kstart := NECK.cinv_start L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kframe := NECK.cinv_frame L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kencw := NECK.cinv_encwrite L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kpb := NECK.call_pb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK PB.
Let Kntb16 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 2 (ne_ntb_u16 EE) NTB16.
Let Kntb32 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 4 (ne_ntb_u32 EE) NTB32.
Let Kntb64 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 8 (ne_ntb_u64 EE) NTB64.
Let Kwts := NECK.call_wts L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK WTS.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rq (Ri : bvmap 5 word) : Prop := getr Ri (PMK.reg 2) = Z_to_bv 64 (sp - 48) /\ getr Ri (PMK.reg 8) = Z_to_bv 64 ov /\ csl Ri.
Lemma rq_call Ra Rb : regs_preserved Ra Rb -> rq Ra -> rq Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_223 ())). Qed.
Lemma rq_piece (KS : list nat) Ra Rb : (forall x, In x KS -> getr Rb (PMK.reg x) = getr Ra (PMK.reg x)) ->
  forallb (fun k => existsb (Nat.eqb k) KS) (2 :: 8 :: CSL)%nat = true -> rq Ra -> rq Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_224 ())). Qed.
Lemma r_call Ra Rb (i : nat) vv : regs_preserved Ra Rb -> In i PMK.cs_all -> getr Ra (PMK.reg i) = vv -> getr Rb (PMK.reg i) = vv.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_225 ())). Qed.

(* [comment removed for export] *)
Lemma st_facts Mq mdq crq kq lo hi : CINV Mq mdq crq kq lo hi ->
  L5.writable RSEGS Mq (sp - 20480) 20480 /\ L5.writable RSEGS Mq ov 56 /\ L5.u64_at RSEGS Mq (ov + 8) osk
  /\ PMSP.model_ok mdq /\ hi_heap HI (NECS.eown en kq ++ LBX) crq Mq (m_vmmaps mdq) /\ L5C.stk (hl_sptop L) Mq sp 20480.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_226 ())). Qed.

Local Ltac bvr Rq := pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 8))) as RB8q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 9))) as RB9q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 10))) as RB10q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 11))) as RB11q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 12))) as RB12q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 18))) as RB18q;
  change (bv_modulus 64) with (2 ^ 64) in RB8q, RB9q, RB10q, RB11q, RB12q, RB18q.

(* [comment removed for export] *)
Lemma mid_piece (pc pc' c : Z) (fxq fx3 : FPState) Rq R3 Mq M3 mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> sp - 48 <= c -> c + 1 <= sp - 32 ->
  mem_grows Mq M3 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (c <= i < c + 1) -> M3 (Z_to_bv 64 i) = Mq (Z_to_bv 64 i)) ->
  msteps RSEGS (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) ->
  (CINV M3 mdq crq kq lo hi -> srealizes RSEGS SCFG (mkCfg (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) mdq) K) ->
  srealizes RSEGS SCFG (mkCfg (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_227 ())). Qed.
(* [comment removed for export] *)
Lemma ro_piece (pc pc' : Z) (fxq fx3 : FPState) Rq R3 Mq M3 mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> (forall a : word, M3 a = Mq a) ->
  msteps RSEGS (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) ->
  (CINV Mq mdq crq kq lo hi -> srealizes RSEGS SCFG (mkCfg (@mkst fx3 R3 (Z_to_bv 64 pc') Mq (seg_rom RSEGS)) mdq) K) ->
  srealizes RSEGS SCFG (mkCfg (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_228 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ev_tail (fxq : FPState) Rq Mq mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> 0 <= lo -> hi <= wb tag v -> rq Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x4013c Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_229 ())). Qed.

(* [comment removed for export] *)
Lemma jtail (pc : Z) (fxq : FPState) Rq Mq mdq crq kq lo hi :
  (pc = 0x400f0 \/ pc = 0x40104 \/ pc = 0x40194 \/ pc = 0x401b4) ->
  CINV Mq mdq crq kq lo hi -> 0 <= lo -> hi <= wb tag v -> rq Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq pc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_230 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x40010 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_231 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem v_uint64_ok : NECS.v_uint64_spec RSEGS CAD AQ EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncU64 ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_232 ())). Qed.
End WithHeap.
End PNSENU64.

End PnSEncU64.
Module PnSEncWsvP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncWsvP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9KS_wsA_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH315regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH319regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsH31C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH31<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH313PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH312F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH313NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH313kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH313ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsH31_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2555regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2559regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9KS_wsH255C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH255<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2553PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2552F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2553NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2553kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7PwsH2553ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP<KS_wsH255_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:KS_wsH255bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8PwsH255b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP=KS_wsH255b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsH16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsH16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsW16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsW16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsJ16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsJ16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsH32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsH323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsH32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsW32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsW323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsW32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsJ32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6PwsJ323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP;KS_wsJ32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7KS_wsL0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:KS_wsL0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7KS_wsL1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP5PwsL13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:KS_wsL1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9KS_wsB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsNC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsN3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9KS_wsN_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsEC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP4PwsE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9KS_wsE_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSEWSP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_233 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_234 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_235 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_236 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_237 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_238 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_239 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_240 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_241 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_242 ())). Qed.
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
Module PwsA := BndP_Ns_098.LibSegNs_wsA.
Definition KS_wsA : list nat := Eval vm_compute in (BG.kept_list 60 PwsA.regs0 PwsA.regs_out0).
Lemma KS_wsA_ok : BG.kept_ok 60 PwsA.regs0 PwsA.regs_out0 KS_wsA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_243 ())). Qed.
Lemma wsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 ->
  L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 536870911 ->
  (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42b3c M) (st fx' R' 0x4472c M')
        /\ (forall x, In x KS_wsA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273260
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_244 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsH31 := BndP_Ns_099.LibSegNs_wsH31.
Definition KS_wsH31 : list nat := Eval vm_compute in (BG.kept_list 60 PwsH31.regs0 PwsH31.regs_out0).
Lemma KS_wsH31_ok : BG.kept_ok 60 PwsH31.regs0 PwsH31.regs_out0 KS_wsH31 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_245 ())). Qed.
Lemma wsH31_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 31 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42b6c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wsH31 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273396
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_246 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsH255 := BndP_Ns_099.LibSegNs_wsH255.
Definition KS_wsH255 : list nat := Eval vm_compute in (BG.kept_list 60 PwsH255.regs0 PwsH255.regs_out0).
Lemma KS_wsH255_ok : BG.kept_ok 60 PwsH255.regs0 PwsH255.regs_out0 KS_wsH255 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_247 ())). Qed.
Lemma wsH255_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 32 <= (V 34%nat) <= 255 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42b6c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wsH255 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273380
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_248 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsH255b := BndP_Ns_099.LibSegNs_wsH255b.
Definition KS_wsH255b : list nat := Eval vm_compute in (BG.kept_list 60 PwsH255b.regs0 PwsH255b.regs_out0).
Lemma KS_wsH255b_ok : BG.kept_ok 60 PwsH255b.regs0 PwsH255b.regs_out0 KS_wsH255b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_249 ())). Qed.
Lemma wsH255b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 32 <= (V 34%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42be4 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wsH255b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273396
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_250 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsH16 := BndP_Ns_099.LibSegNs_wsH16.
Definition KS_wsH16 : list nat := Eval vm_compute in (BG.kept_list 60 PwsH16.regs0 PwsH16.regs_out0).
Lemma KS_wsH16_ok : BG.kept_ok 60 PwsH16.regs0 PwsH16.regs_out0 KS_wsH16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_251 ())). Qed.
Lemma wsH16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 256 <= (V 34%nat) <= 65535 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42b6c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wsH16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273492
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_252 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsW16 := BndP_Ns_099.LibSegNs_wsW16.
Definition KS_wsW16 : list nat := Eval vm_compute in (BG.kept_list 60 PwsW16.regs0 PwsW16.regs_out0).
Lemma KS_wsW16_ok : BG.kept_ok 60 PwsW16.regs0 PwsW16.regs_out0 KS_wsW16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_253 ())). Qed.
Lemma wsW16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42c54 M) (st fx' R' 0x41aec M')
        /\ (forall x, In x KS_wsW16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273504
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_254 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsJ16 := BndP_Ns_099.LibSegNs_wsJ16.
Definition KS_wsJ16 : list nat := Eval vm_compute in (BG.kept_list 60 PwsJ16.regs0 PwsJ16.regs_out0).
Lemma KS_wsJ16_ok : BG.kept_ok 60 PwsJ16.regs0 PwsJ16.regs_out0 KS_wsJ16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_255 ())). Qed.
Lemma wsJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42c60 M) (st fx' R' 0x42c00 M')
        /\ (forall x, In x KS_wsJ16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_256 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsH32 := BndP_Ns_099.LibSegNs_wsH32.
Definition KS_wsH32 : list nat := Eval vm_compute in (BG.kept_list 60 PwsH32.regs0 PwsH32.regs_out0).
Lemma KS_wsH32_ok : BG.kept_ok 60 PwsH32.regs0 PwsH32.regs_out0 KS_wsH32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_257 ())). Qed.
Lemma wsH32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 65536 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42b6c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wsH32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273344
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_258 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsW32 := BndP_Ns_099.LibSegNs_wsW32.
Definition KS_wsW32 : list nat := Eval vm_compute in (BG.kept_list 60 PwsW32.regs0 PwsW32.regs_out0).
Lemma KS_wsW32_ok : BG.kept_ok 60 PwsW32.regs0 PwsW32.regs_out0 KS_wsW32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_259 ())). Qed.
Lemma wsW32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42bc0 M) (st fx' R' 0x41b50 M')
        /\ (forall x, In x KS_wsW32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273356
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_260 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsJ32 := BndP_Ns_099.LibSegNs_wsJ32.
Definition KS_wsJ32 : list nat := Eval vm_compute in (BG.kept_list 60 PwsJ32.regs0 PwsJ32.regs_out0).
Lemma KS_wsJ32_ok : BG.kept_ok 60 PwsJ32.regs0 PwsJ32.regs_out0 KS_wsJ32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_261 ())). Qed.
Lemma wsJ32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42bcc M) (st fx' R' 0x42c00 M')
        /\ (forall x, In x KS_wsJ32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_262 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsL0 := BndP_Ns_099.LibSegNs_wsL0.
Definition KS_wsL0 : list nat := Eval vm_compute in (BG.kept_list 60 PwsL0.regs0 PwsL0.regs_out0).
Lemma KS_wsL0_ok : BG.kept_ok 60 PwsL0.regs0 PwsL0.regs_out0 KS_wsL0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_263 ())). Qed.
Lemma wsL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 11%nat) <= 140737488355312 ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) 0 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42bf4 M) (st fx' R' 0x42c38 M')
        /\ (forall x, In x KS_wsL0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_264 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsL1 := BndP_Ns_099.LibSegNs_wsL1.
Definition KS_wsL1 : list nat := Eval vm_compute in (BG.kept_list 60 PwsL1.regs0 PwsL1.regs_out0).
Lemma KS_wsL1_ok : BG.kept_ok 60 PwsL1.regs0 PwsL1.regs_out0 KS_wsL1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_265 ())). Qed.
Lemma wsL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42bf4 M) (st fx' R' 0x42c00 M')
        /\ (forall x, In x KS_wsL1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_266 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsB := BndP_Ns_098.LibSegNs_wsB.
Definition KS_wsB : list nat := Eval vm_compute in (BG.kept_list 60 PwsB.regs0 PwsB.regs_out0).
Lemma KS_wsB_ok : BG.kept_ok 60 PwsB.regs0 PwsB.regs_out0 KS_wsB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_267 ())). Qed.
Lemma wsB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 1 <= (V 36%nat) <= 140737488355327 -> L5.u8_at RSEGS M (V 36%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> 1 <= (V 38%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42c00 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wsB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 273428
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_268 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsN := BndP_Ns_099.LibSegNs_wsN.
Definition KS_wsN : list nat := Eval vm_compute in (BG.kept_list 60 PwsN.regs0 PwsN.regs_out0).
Lemma KS_wsN_ok : BG.kept_ok 60 PwsN.regs0 PwsN.regs_out0 KS_wsN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_269 ())). Qed.
Lemma wsN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1 <= (V 36%nat) <= 140737488355327 -> 2 <= (V 38%nat) <= 536870911 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42c14 M) (st fx' R' 0x42c00 M')
        /\ (forall x, In x KS_wsN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 38%nat) - 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_270 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwsE := BndP_Ns_098.LibSegNs_wsE.
Definition KS_wsE : list nat := Eval vm_compute in (BG.kept_list 60 PwsE.regs0 PwsE.regs_out0).
Lemma KS_wsE_ok : BG.kept_ok 60 PwsE.regs0 PwsE.regs_out0 KS_wsE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_271 ())). Qed.
Lemma wsE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 1 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 1 <= (V 36%nat) <= 140737488355327 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x42c14 M) (st fx' R' 0x42c38 M')
        /\ (forall x, In x KS_wsE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsvP ()) [] (Mh_0185_blobs1.kr_b_272 ())). Qed.
(* [comment removed for export] *)

End PNSEWSP.

End PnSEncWsvP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef.
Module PnSEncWsv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146.PnEncCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.PnCValSpecW OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSEncWsvP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019.Ns0_code_42af4_42c70.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncWsv () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK8cells_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib5Lists7ListDef6Forall00I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4kctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI45stdpp9bitvector;definitions2bv00C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbc69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3CSLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indI47Corelib4Init5Logic5False00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List:in_app_iffI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7view_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyK47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;brange_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR5ag_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_ltI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019DNs0_code_42af4_42c707W_42bf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019DNs0_code_42af4_42c707F_42bf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019DNs0_code_42af4_42c707D_42bf0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV8st_factsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8wsE_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV6CSLsubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsEC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses8or_morphc69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8wsB_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4cinvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib6ZArith6Zorder9Zle_0_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV7CSLcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV6tail_EC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8wsN_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP6KS_wsNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV3COKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9wsL0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP9wsL1_concC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsJ16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP:wsJ32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV4loopC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7KS_wsL1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsJ16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP8KS_wsJ32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWsvP7PNSEWSP7KS_wsL0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWsv7PNSEWSV4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayoutEne_write_string_valueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8wsv_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01". Local Ltac lia := L5FastLia.plia.

Module PNSEWSV.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac insub := intros ? Hx; rewrite ?in_app_iff in Hx; rewrite ?in_app_iff; tauto.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis PO : NESK.sink_policy_ok P.
Hypothesis HBS : NESK.sp_hb P NESK.SMZ.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
(* [comment removed for export] *)
Hypothesis PB : NESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P.
Hypothesis NTB16 : NECS.ntb_spec RSEGS CAD L HI P 2 (ne_ntb_u16 EE).
Hypothesis NTB32 : NECS.ntb_spec RSEGS CAD L HI P 4 (ne_ntb_u32 EE).
Hypothesis VALE : PECVSW.validate_fun_specW RSEGS CAD L (ne_validate_enc EE).   (* [comment removed for export] *)

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).

Section Call.
Hypothesis SPM : NESK.sp_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk p d n : Z) (bs : list Z) (en : enc) (k : NESK.sink).
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 3.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 p.
Hypothesis Hp1 : sp <= p.
Hypothesis Hp2 : p + 16 <= ov.
Hypothesis VOK : NECS.view_ok RSEGS M sp ov LBX p d n.
Hypothesis BS : L5.bytes_at RSEGS M d bs.
Hypothesis BSL : Z.of_nat (length bs) = n.
Hypothesis UTF : utf8_valid bs = true.
Hypothesis BOK : bytes_ok bs.
Hypothesis Hov1 : sp <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : ov mod 8 = 0.
Hypothesis Hosk1 : sp <= osk.
Hypothesis Hosk2 : osk + 24 <= hl_sptop L.
Hypothesis Hosk3 : osk mod 8 = 0.
Hypothesis SEP2 : ov + 56 <= osk.
Hypothesis EA : enc_at M ov osk en.
Hypothesis SKA : sink_atP M osk k.
Hypothesis BASE : PMST.base_ok RSEGS CAD M.
Hypothesis PRE : NESK.sk_z k + hdr_str n + n <= NESK.SMZ.   (* [comment removed for export] *)
Hypothesis CRED : PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (k' : NESK.sink) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en -> sink_atP M' osk k' -> NESK.sk_z k' = NESK.sk_z k + hdr_str n + n ->
        L5C.hpres L LBX sp (PMSP.pm_scr 3) [(osk, 24)] M M' ->
        PMSP.credit_keep cr cr' (NESK.sink_pot P (NESK.sk_c k)) (NESK.sink_pot P (NESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Let cells : list (Z * Z) := [(sp - 8, bv_unsigned (getr R (PMK.reg 1))); (sp - 16, bv_unsigned (getr R (PMK.reg 8))); (sp - 24, bv_unsigned (getr R (PMK.reg 9)));
                             (sp - 32, bv_unsigned (getr R (PMK.reg 18))); (sp - 40, bv_unsigned (getr R (PMK.reg 19)))].
Let CINV := (NECK.cinv L HI P M model LBX cr sp ov osk en k 18432 cells).
Lemma COK : NECK.cells_ok sp 64 cells.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_273 ())). Qed.
Lemma CXok : NECK.kctx L HI P R M model K LBX cr sp r ov osk en k 3 18432 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_274 ())). Qed.
Let Kfacts := NECK.facts_ok L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok.
Let Kstart := NECK.cinv_start L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok.
Let Kframe := NECK.cinv_frame L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok.
Let Khpres := NECK.fin_hpres L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok.
Let Kpb := NECK.call_pb L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok cells COK PB.
Let Kntb16 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok cells COK 2 (ne_ntb_u16 EE) NTB16.
Let Kntb32 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 3 18432 64 CXok cells COK 4 (ne_ntb_u32 EE) NTB32.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

Lemma CSLsub KS Ra Rb : (forall x, In x KS -> getr Rb (PMK.reg x) = getr Ra (PMK.reg x)) -> forallb (fun k0 => existsb (Nat.eqb k0) KS) CSL = true -> csl Ra -> csl Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_275 ())). Qed.
Lemma CSLcall Ra Rb : regs_preserved Ra Rb -> csl Ra -> csl Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_276 ())). Qed.

(* [comment removed for export] *)
Lemma st_facts Mq mdq crq kq lo hi : CINV Mq mdq crq kq lo hi ->
  L5.writable RSEGS Mq (sp - 18432) 18432 /\ L5.writable RSEGS Mq ov 56 /\ L5.u64_at RSEGS Mq (ov + 8) osk
  /\ PMSP.model_ok mdq /\ hi_heap HI (NECS.eown en kq ++ LBX) crq Mq (m_vmmaps mdq) /\ L5C.stk (hl_sptop L) Mq sp 18432
  /\ L5.u64_at RSEGS Mq (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\ L5.u64_at RSEGS Mq (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS Mq (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS Mq (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS Mq (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
  /\ L5.u64_at RSEGS Mq p d /\ L5.u64_at RSEGS Mq (p + 8) n /\ L5.bytes_at RSEGS Mq d bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_277 ())). Qed.

(* [comment removed for export] *)
Lemma fin (fx7 : FPState) R7 M7 md7 cr7 k7 w :
  CINV M7 md7 cr7 k7 w w -> w = hdr_str n + n ->
  getr R7 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1))) -> getr R7 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R7 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R7 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R7 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R7 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) -> csl R7 ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 0x42c38 M7 md7) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_278 ())). Qed.

(* [comment removed for export] *)
Lemma tail_E (fxq : FPState) Rq Mq mdq crq kq w c :
  CINV Mq mdq crq kq w w -> w = hdr_str n + n ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 c -> 1 <= c < 2 ^ 47 ->
  getr Rq (PMK.reg 18) = Z_to_bv 64 1 -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x42c14 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_279 ())). Qed.

(* [comment removed for export] *)
Lemma loop (j : nat) : forall (fxq : FPState) Rq Mq mdq crq kq w,
  (1 <= j)%nat -> Z.of_nat j <= n ->
  CINV Mq mdq crq kq w w -> w + Z.of_nat j = hdr_str n + n -> 0 <= w ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 (d + (n - Z.of_nat j)) ->
  getr Rq (PMK.reg 18) = Z_to_bv 64 (Z.of_nat j) -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x42c00 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_280 ())). Qed.

(* [comment removed for export] *)
Lemma at_L (fxq : FPState) Rq Mq mdq crq kq (pc : Z) :
  (pc = 0x42bf4 \/ pc = 0x42c60 \/ pc = 0x42bcc) -> (pc = 0x42bf4 \/ 1 <= n) ->
  CINV Mq mdq crq kq (hdr_str n) (hdr_str n) ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 p -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq pc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_281 ())). Qed.

(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x42b3c M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_282 ())). Qed.
End Call.


(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem wsv_ok : NECS.wsv_spec RSEGS CAD EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWsv ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_283 ())). Qed.
End WithHeap.
End PNSEWSV.

End PnSEncWsv.
Module PnSEncWtsP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncWtsP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8KS_wtA_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8KS_wtA_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8KS_wtA_2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List<nth_error_InI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP;KS_wtA_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP;KS_wtA_1_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtA3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP;KS_wtA_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3aC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt3a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt3b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3cC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3c3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt3c_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3zC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt3z3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt3z_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt6aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt6a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt6bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt6b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt6cC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt6c3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt6c_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt9a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt9b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9cC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9c3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt9c_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9dC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9d3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt9d_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9eC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP5Pwt9e3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP:KS_wt9e_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP6KS_wtZC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP4PwtZ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9KS_wtZ_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSEWTP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_284 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_285 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_286 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_287 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_288 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_289 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_290 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_291 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_292 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_293 ())). Qed.
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
Module PwtA := BndP_Ns_100.LibSegNs_wtA.
Definition KS_wtA_0 : list nat := Eval vm_compute in (BG.kept_list 60 PwtA.regs0 PwtA.regs_out0).
Lemma KS_wtA_0_ok : BG.kept_ok 60 PwtA.regs0 PwtA.regs_out0 KS_wtA_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_294 ())). Qed.
Definition KS_wtA_1 : list nat := Eval vm_compute in (BG.kept_list 60 PwtA.regs0 PwtA.regs_out1).
Lemma KS_wtA_1_ok : BG.kept_ok 60 PwtA.regs0 PwtA.regs_out1 KS_wtA_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_295 ())). Qed.
Definition KS_wtA_2 : list nat := Eval vm_compute in (BG.kept_list 60 PwtA.regs0 PwtA.regs_out2).
Lemma KS_wtA_2_ok : BG.kept_ok 60 PwtA.regs0 PwtA.regs_out2 KS_wtA_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_296 ())). Qed.
Lemma wtA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 18446744073709551615 -> 0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x41e18 M) (st fx' R' 0x41e90 M')
        /\ (forall x, In x KS_wtA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 12)
        /\ getr R' (reg 18) = getr R (reg 10)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x41e18 M) (st fx' R' 0x41ee8 M')
        /\ (forall x, In x KS_wtA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = getr R (reg 10)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x41e18 M) (st fx' R' 0x41e5c M')
        /\ (forall x, In x KS_wtA_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = getr R (reg 10)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_297 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt3a := BndP_Ns_099.LibSegNs_wt3a.
Definition KS_wt3a : list nat := Eval vm_compute in (BG.kept_list 60 Pwt3a.regs0 Pwt3a.regs_out0).
Lemma KS_wt3a_ok : BG.kept_ok 60 Pwt3a.regs0 Pwt3a.regs_out0 KS_wt3a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_298 ())). Qed.
Lemma wt3a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 47) <= bv_unsigned a < ((V 2%nat) - 47) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 47) <= i < ((V 2%nat) - 47) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41e5c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt3a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 269932
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 47)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_299 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt3b := BndP_Ns_099.LibSegNs_wt3b.
Definition KS_wt3b : list nat := Eval vm_compute in (BG.kept_list 60 Pwt3b.regs0 Pwt3b.regs_out0).
Lemma KS_wt3b_ok : BG.kept_ok 60 Pwt3b.regs0 Pwt3b.regs_out0 KS_wt3b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_300 ())). Qed.
Lemma wt3b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 46) <= bv_unsigned a < ((V 2%nat) - 46) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 46) <= i < ((V 2%nat) - 46) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41e6c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt3b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 269952
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 46)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_301 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt3c := BndP_Ns_100.LibSegNs_wt3c.
Definition KS_wt3c : list nat := Eval vm_compute in (BG.kept_list 60 Pwt3c.regs0 Pwt3c.regs_out0).
Lemma KS_wt3c_ok : BG.kept_ok 60 Pwt3c.regs0 Pwt3c.regs_out0 KS_wt3c = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_302 ())). Qed.
Lemma wt3c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 0 <= (V 11%nat) <= 18446744073709551615 ->
  0 <= (V 12%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41e80 M) (st fx' R' 0x41b50 M')
        /\ (forall x, In x KS_wt3c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 269964
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_303 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt3z := BndP_Ns_100.LibSegNs_wt3z.
Definition KS_wt3z : list nat := Eval vm_compute in (BG.kept_list 60 Pwt3z.regs0 Pwt3z.regs_out0).
Lemma KS_wt3z_ok : BG.kept_ok 60 Pwt3z.regs0 Pwt3z.regs_out0 KS_wt3z = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_304 ())). Qed.
Lemma wt3z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 59%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41e8c M) (st fx' R' 0x41f30 M')
        /\ (forall x, In x KS_wt3z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_305 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt6a := BndP_Ns_100.LibSegNs_wt6a.
Definition KS_wt6a : list nat := Eval vm_compute in (BG.kept_list 60 Pwt6a.regs0 Pwt6a.regs_out0).
Lemma KS_wt6a_ok : BG.kept_ok 60 Pwt6a.regs0 Pwt6a.regs_out0 KS_wt6a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_306 ())). Qed.
Lemma wt6a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 45) <= bv_unsigned a < ((V 2%nat) - 45) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 45) <= i < ((V 2%nat) - 45) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41ee8 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt6a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270072
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 45)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_307 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt6b := BndP_Ns_100.LibSegNs_wt6b.
Definition KS_wt6b : list nat := Eval vm_compute in (BG.kept_list 60 Pwt6b.regs0 Pwt6b.regs_out0).
Lemma KS_wt6b_ok : BG.kept_ok 60 Pwt6b.regs0 Pwt6b.regs_out0 KS_wt6b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_308 ())). Qed.
Lemma wt6b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 44) <= bv_unsigned a < ((V 2%nat) - 44) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 44) <= i < ((V 2%nat) - 44) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41ef8 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt6b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270092
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 44)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_309 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt6c := BndP_Ns_100.LibSegNs_wt6c.
Definition KS_wt6c : list nat := Eval vm_compute in (BG.kept_list 60 Pwt6c.regs0 Pwt6c.regs_out0).
Lemma KS_wt6c_ok : BG.kept_ok 60 Pwt6c.regs0 Pwt6c.regs_out0 KS_wt6c = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_310 ())). Qed.
Lemma wt6c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 10%nat) + 8) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41f0c M) (st fx' R' 0x41f34 M')
        /\ (forall x, In x KS_wt6c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270104
        /\ getr R' (reg 10) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_311 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt9a := BndP_Ns_100.LibSegNs_wt9a.
Definition KS_wt9a : list nat := Eval vm_compute in (BG.kept_list 60 Pwt9a.regs0 Pwt9a.regs_out0).
Lemma KS_wt9a_ok : BG.kept_ok 60 Pwt9a.regs0 Pwt9a.regs_out0 KS_wt9a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_312 ())). Qed.
Lemma wt9a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 12%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 43) <= bv_unsigned a < ((V 2%nat) - 43) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 43) <= i < ((V 2%nat) - 43) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41e90 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt9a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 269992
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 43)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_313 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt9b := BndP_Ns_100.LibSegNs_wt9b.
Definition KS_wt9b : list nat := Eval vm_compute in (BG.kept_list 60 Pwt9b.regs0 Pwt9b.regs_out0).
Lemma KS_wt9b_ok : BG.kept_ok 60 Pwt9b.regs0 Pwt9b.regs_out0 KS_wt9b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_314 ())). Qed.
Lemma wt9b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 12%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 42) <= bv_unsigned a < ((V 2%nat) - 42) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 42) <= i < ((V 2%nat) - 42) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41ea8 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt9b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270012
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 42)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_315 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt9c := BndP_Ns_100.LibSegNs_wt9c.
Definition KS_wt9c : list nat := Eval vm_compute in (BG.kept_list 60 Pwt9c.regs0 Pwt9c.regs_out0).
Lemma KS_wt9c_ok : BG.kept_ok 60 Pwt9c.regs0 Pwt9c.regs_out0 KS_wt9c = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_316 ())). Qed.
Lemma wt9c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 12%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41ebc M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_wt9c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270032
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_317 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt9d := BndP_Ns_100.LibSegNs_wt9d.
Definition KS_wt9d : list nat := Eval vm_compute in (BG.kept_list 60 Pwt9d.regs0 Pwt9d.regs_out0).
Lemma KS_wt9d_ok : BG.kept_ok 60 Pwt9d.regs0 Pwt9d.regs_out0 KS_wt9d = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_318 ())). Qed.
Lemma wt9d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 12%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 0 <= (V 11%nat) <= 18446744073709551615 ->
  0 <= (V 12%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41ed0 M) (st fx' R' 0x41b50 M')
        /\ (forall x, In x KS_wt9d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270044
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_319 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pwt9e := BndP_Ns_100.LibSegNs_wt9e.
Definition KS_wt9e : list nat := Eval vm_compute in (BG.kept_list 60 Pwt9e.regs0 Pwt9e.regs_out0).
Lemma KS_wt9e_ok : BG.kept_ok 60 Pwt9e.regs0 Pwt9e.regs_out0 KS_wt9e = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_320 ())). Qed.
Lemma wt9e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 12%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41edc M) (st fx' R' 0x41f34 M')
        /\ (forall x, In x KS_wt9e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 270104
        /\ getr R' (reg 10) = Z_to_bv 64 (V 11%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_321 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PwtZ := BndP_Ns_100.LibSegNs_wtZ.
Definition KS_wtZ : list nat := Eval vm_compute in (BG.kept_list 60 PwtZ.regs0 PwtZ.regs_out0).
Lemma KS_wtZ_ok : BG.kept_ok 60 PwtZ.regs0 PwtZ.regs_out0 KS_wtZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_322 ())). Qed.
Lemma wtZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 11%nat) -> getr R (reg 9) = Z_to_bv 64 (V 59%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 10%nat) -> getr R (reg 19) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x41f18 M) (st fx' R' 0x41f30 M')
        /\ (forall x, In x KS_wtZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWtsP ()) [] (Mh_0185_blobs1.kr_b_323 ())). Qed.
(* [comment removed for export] *)

End PNSEWTP.

End PnSEncWtsP.
Module PnSEncWts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146.PnEncCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSEncWtsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0019.Ns0_code_41aa4_42408.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncWts () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK8cells_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib5Lists7ListDef6Forall00I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4kctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS3cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init5Logic2or00C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indI47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS3CSLC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019DNs0_code_41aa4_424087W_41ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019DNs0_code_41aa4_424087F_41ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0019DNs0_code_41aa4_424087D_41ee8C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C46Stdlib5Lists4List:Forall_invC46Stdlib5Lists4List?Forall_inv_tailC69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8wtZ_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt3z_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP6KS_wtZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS2rqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS8st_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS3COKC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt9a_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS8rq_pieceC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4cinvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS7rq_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS6r_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt9b_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt9c_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt9d_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt9e_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS8epilogueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS8ro_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS9mid_pieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9dC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt9eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt6a_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt6b_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt6c_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt6aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt6bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt6cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt3a_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt3b_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP9wt3c_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP7KS_wt3cC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8wtA_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS6path96C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS6path64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS6path32C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8KS_wtA_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8KS_wtA_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185:PnSEncWtsP7PNSEWTP8KS_wtA_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc69OSSVerify5KrLib7Mh_01859PnSEncWts7PNSEWTS4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayoutBne_write_timestampC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECSDwrite_timestamp_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSEWTS.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Local Ltac post_of P := destruct P as (fxpq & Rpq & Mpq & HPpq); exists fxpq, Rpq, Mpq; decompose [and] HPpq; repeat (split; [assumption|]); assumption.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : NESK.sink_policy.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis PO : NESK.sink_policy_ok P.
Hypothesis HBS : NESK.sp_hb P NESK.SMZ.
Let KL := PMKS.klayout_S L LY.
(* [comment removed for export] *)
Hypothesis PB : NESK.push_back_spec RSEGS CAD EE L HI PMSP.T3 PMSP.T4 P.
Hypothesis NTB32 : NECS.ntb_spec RSEGS CAD L HI P 4 (ne_ntb_u32 EE).
Hypothesis NTB64 : NECS.ntb_spec RSEGS CAD L HI P 8 (ne_ntb_u64 EE).

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).

Section Call.
Hypothesis SPM : NESK.sp_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk sec nano : Z).
Variables (en : enc) (k : NESK.sink).
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 3.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 sec.
Hypothesis A12 : getr R 12%bv = Z_to_bv 64 nano.
Hypothesis Hsec : 0 <= sec < 2 ^ 64.
Hypothesis Hnano : 0 <= nano < 2 ^ 64.
Hypothesis Hov1 : sp <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : ov mod 8 = 0.
Hypothesis Hosk1 : sp <= osk.
Hypothesis Hosk2 : osk + 24 <= hl_sptop L.
Hypothesis Hosk3 : osk mod 8 = 0.
Hypothesis SEP2 : ov + 56 <= osk.
Hypothesis EA : enc_at M ov osk en.
Hypothesis SKA : sink_atP M osk k.
Hypothesis PRE : NESK.sk_z k + 15 <= NESK.SMZ.
Hypothesis CRED : PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (k' : NESK.sink) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en -> sink_atP M' osk k' -> NESK.sk_z k + 6 <= NESK.sk_z k' <= NESK.sk_z k + 15 ->
        L5C.hpres L LBX sp (PMSP.pm_scr 3) [(osk, 24)] M M' ->
        PMSP.credit_keep cr cr' (NESK.sink_pot P (NESK.sk_c k)) (NESK.sink_pot P (NESK.sk_c k')) ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Let cells : list (Z * Z) := [(sp - 8, bv_unsigned (getr R (PMK.reg 1))); (sp - 16, bv_unsigned (getr R (PMK.reg 8))); (sp - 24, bv_unsigned (getr R (PMK.reg 9)));
                             (sp - 32, bv_unsigned (getr R (PMK.reg 18))); (sp - 40, bv_unsigned (getr R (PMK.reg 19)))].
Let CINV := (NECK.cinv L HI P M model LBX cr sp ov osk en k 18432 cells).
Lemma COK : NECK.cells_ok sp 48 cells.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_324 ())). Qed.
Lemma CXok : NECK.kctx L HI P R M model K LBX cr sp r ov osk en k 3 18432 48.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_325 ())). Qed.
Let Kfacts := NECK.facts_ok L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok.
Let Khp := NECK.fin_hpres L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok.
Let Kstart := NECK.cinv_start L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok.
Let Kframe := NECK.cinv_frame L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok.
Let Kpb := NECK.call_pb L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok cells COK PB.
Let Kntb32 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok cells COK 4 (ne_ntb_u32 EE) NTB32.
Let Kntb64 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 3 18432 48 CXok cells COK 8 (ne_ntb_u64 EE) NTB64.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

(* [comment removed for export] *)
Lemma fin (fx7 : FPState) R7 M7 md7 cr7 k7 zlo zhi :
  CINV M7 md7 cr7 k7 zlo zhi -> 6 <= zlo -> zhi <= 15 ->
  getr R7 (PMK.reg 1) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 1))) -> getr R7 (PMK.reg 2) = Z_to_bv 64 sp ->
  getr R7 (PMK.reg 8) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 8))) -> getr R7 (PMK.reg 9) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 9))) ->
  getr R7 (PMK.reg 18) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 18))) -> getr R7 (PMK.reg 19) = Z_to_bv 64 (bv_unsigned (getr R (PMK.reg 19))) ->
  csl R7 ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 0x41f30 M7 md7) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_326 ())). Qed.

(* [comment removed for export] *)
Lemma epilogue (pc : Z) (fxq : FPState) Rq Mq mdq crq kq zlo zhi :
  (pc = 0x41f18 \/ pc = 0x41e8c) ->
  CINV Mq mdq crq kq zlo zhi -> 6 <= zlo -> zhi <= 15 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr Rq (PMK.reg 18) = Z_to_bv 64 ov -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq pc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_327 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rq (Ri : bvmap 5 word) : Prop := getr Ri (PMK.reg 2) = Z_to_bv 64 (sp - 48) /\ getr Ri (PMK.reg 18) = Z_to_bv 64 ov /\ csl Ri.
Lemma rq_call Ra Rb : regs_preserved Ra Rb -> rq Ra -> rq Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_328 ())). Qed.
Lemma rq_piece (KS : list nat) Ra Rb : (forall x, In x KS -> getr Rb (PMK.reg x) = getr Ra (PMK.reg x)) ->
  forallb (fun k => existsb (Nat.eqb k) KS) (2 :: 18 :: CSL)%nat = true -> rq Ra -> rq Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_329 ())). Qed.
Lemma r_call Ra Rb (i : nat) v : regs_preserved Ra Rb -> In i PMK.cs_all -> getr Ra (PMK.reg i) = v -> getr Rb (PMK.reg i) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_330 ())). Qed.

(* [comment removed for export] *)
Lemma st_facts Mq mdq crq kq lo hi : CINV Mq mdq crq kq lo hi ->
  L5.writable RSEGS Mq (sp - 18432) 18432 /\ L5.writable RSEGS Mq ov 56 /\ L5.u64_at RSEGS Mq (ov + 8) osk
  /\ PMSP.model_ok mdq /\ hi_heap HI (NECS.eown en kq ++ LBX) crq Mq (m_vmmaps mdq) /\ L5C.stk (hl_sptop L) Mq sp 18432.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_331 ())). Qed.

Local Ltac bvr Rq := pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 8))) as RB8q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 9))) as RB9q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 10))) as RB10q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 11))) as RB11q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 12))) as RB12q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 19))) as RB19q;
  change (bv_modulus 64) with (2 ^ 64) in RB8q, RB9q, RB10q, RB11q, RB12q, RB19q.

(* [comment removed for export] *)
Lemma mid_piece (pc pc' c : Z) (fxq fx3 : FPState) Rq R3 Mq M3 mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> sp - 48 <= c -> c + 1 <= sp - 40 ->
  mem_grows Mq M3 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (c <= i < c + 1) -> M3 (Z_to_bv 64 i) = Mq (Z_to_bv 64 i)) ->
  msteps RSEGS (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) ->
  (CINV M3 mdq crq kq lo hi -> srealizes RSEGS SCFG (mkCfg (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) mdq) K) ->
  srealizes RSEGS SCFG (mkCfg (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_332 ())). Qed.
(* [comment removed for export] *)
Lemma ro_piece (pc pc' : Z) (fxq fx3 : FPState) Rq R3 Mq M3 mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> (forall a : word, M3 a = Mq a) ->
  msteps RSEGS (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 pc') M3 (seg_rom RSEGS)) ->
  (CINV Mq mdq crq kq lo hi -> srealizes RSEGS SCFG (mkCfg (@mkst fx3 R3 (Z_to_bv 64 pc') Mq (seg_rom RSEGS)) mdq) K) ->
  srealizes RSEGS SCFG (mkCfg (@mkst fxq Rq (Z_to_bv 64 pc) Mq (seg_rom RSEGS)) mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_333 ())). Qed.

(* [comment removed for export] *)
Lemma path96 (fxq : FPState) Rq Mq mdq crq kq :
  CINV Mq mdq crq kq 0 0 -> rq Rq -> srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x41e90 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_334 ())). Qed.

(* [comment removed for export] *)
Lemma path64 (fxq : FPState) Rq Mq mdq crq kq :
  CINV Mq mdq crq kq 0 0 -> rq Rq -> getr Rq (PMK.reg 9) = Z_to_bv 64 (ov + 8) -> getr Rq (PMK.reg 10) = Z_to_bv 64 osk ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x41ee8 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_335 ())). Qed.

(* [comment removed for export] *)
Lemma path32 (fxq : FPState) Rq Mq mdq crq kq :
  CINV Mq mdq crq kq 0 0 -> rq Rq -> getr Rq (PMK.reg 9) = Z_to_bv 64 (ov + 8) -> getr Rq (PMK.reg 10) = Z_to_bv 64 osk ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x41e5c Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_336 ())). Qed.

(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x41e18 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_337 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem write_timestamp_ok : NECS.write_timestamp_spec RSEGS CAD EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncWts ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_338 ())). Qed.
End WithHeap.
End PNSEWTS.

End PnSEncWts.
Module PnSrcSXsgetnP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0165.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSrcSXsgetnP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelK47Corelib4Init5Logic3and01C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgA0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlK47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP=word_of_zpolyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K47Corelib4Init5Logic4True01c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP:KS_xgA0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgA1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA16cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP:KS_xgA1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgA2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgA23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP:KS_xgA2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgC1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP:KS_xgC1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP7KS_xgC2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP5PxgC23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0185=PnSrcSXsgetnP6PMSXGP:KS_xgC2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PMSXGP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_339 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_340 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_341 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_342 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_343 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_344 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_345 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_346 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_347 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_348 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_349 ())). Qed.
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
Module PxgA0 := BndP_Ns_100.LibSegNs_xgA0.
Definition KS_xgA0 : list nat := Eval vm_compute in (BG.kept_list 48 PxgA0.regs0 PxgA0.regs_out0).
Lemma KS_xgA0_ok : BG.kept_ok 48 PxgA0.regs0 PxgA0.regs_out0 KS_xgA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_350 ())). Qed.
Lemma xgA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 814272 -> L5.u64_at RSEGS M (V 36%nat) 800152 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) (V 33%nat) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> 4096 <= (V 33%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6ba54 M) (st fx' R' 0x6bb5c M')
        /\ (forall x, In x KS_xgA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 441068
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_351 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgA1 := BndP_Ns_100.LibSegNs_xgA1.
Definition KS_xgA1 : list nat := Eval vm_compute in (BG.kept_list 48 PxgA1.regs0 PxgA1.regs_out0).
Lemma KS_xgA1_ok : BG.kept_ok 48 PxgA1.regs0 PxgA1.regs_out0 KS_xgA1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_352 ())). Qed.
Lemma xgA1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 814272 -> L5.u64_at RSEGS M (V 36%nat) 800152 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) ((V 33%nat) + (V 35%nat)) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> 4096 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6ba54 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_xgA1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 441128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 16384
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 2147483647
        /\ getr R' (reg 22) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_353 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgA2 := BndP_Ns_101.LibSegNs_xgA2.
Definition KS_xgA2 : list nat := Eval vm_compute in (BG.kept_list 48 PxgA2.regs0 PxgA2.regs_out0).
Lemma KS_xgA2_ok : BG.kept_ok 48 PxgA2.regs0 PxgA2.regs_out0 KS_xgA2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_354 ())). Qed.
Lemma xgA2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 814272 -> L5.u64_at RSEGS M (V 36%nat) 800152 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) ((V 33%nat) + (V 35%nat)) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> 4096 <= (V 33%nat) <= 140737488355328 -> 16385 <= (V 35%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6ba54 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_xgA2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 441128
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 16384
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 16384
        /\ getr R' (reg 21) = Z_to_bv 64 2147483647
        /\ getr R' (reg 22) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_355 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgC1 := BndP_Ns_101.LibSegNs_xgC1.
Definition KS_xgC1 : list nat := Eval vm_compute in (BG.kept_list 48 PxgC1.regs0 PxgC1.regs_out0).
Lemma KS_xgC1_ok : BG.kept_ok 48 PxgC1.regs0 PxgC1.regs_out0 KS_xgC1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_356 ())). Qed.
Lemma xgC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 2147483647 -> getr R (reg 22) = Z_to_bv 64 18446744073709551615 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 814272 -> L5.u64_at RSEGS M (V 36%nat) 800152 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) (V 34%nat) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> L5.writable RSEGS M ((V 36%nat) + 24) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6bb28 M) (st fx' R' 0x6bb5c M')
        /\ (forall x, In x KS_xgC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 24) ((V 33%nat) + 16384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_357 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PxgC2 := BndP_Ns_101.LibSegNs_xgC2.
Definition KS_xgC2 : list nat := Eval vm_compute in (BG.kept_list 48 PxgC2.regs0 PxgC2.regs_out0).
Lemma KS_xgC2_ok : BG.kept_ok 48 PxgC2.regs0 PxgC2.regs_out0 KS_xgC2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_358 ())). Qed.
Lemma xgC2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 16384 -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 2147483647 -> getr R (reg 22) = Z_to_bv 64 18446744073709551615 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (V 36%nat) <= 140737488355072 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 256 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 814272 -> L5.u64_at RSEGS M (V 36%nat) 800152 ->
  L5.u64_at RSEGS M ((V 36%nat) + 24) (V 33%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 32) ((V 33%nat) + (V 35%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 48) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 88) ((V 33%nat) + (V 35%nat)) ->
  L5.u32_at RSEGS M ((V 36%nat) + 96) 8 -> L5.writable RSEGS M ((V 36%nat) + 24) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 39%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) -> 4096 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 35%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6bb28 M) (st fx' R' 0x6bb5c M')
        /\ (forall x, In x KS_xgC2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 441068
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 24) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSrcSXsgetnP ()) [] (Mh_0185_blobs1.kr_b_359 ())). Qed.
(* [comment removed for export] *)

End PMSXGP.

End PnSrcSXsgetnP.
Module PnSrcSXsgetn.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnParSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0185.PnSrcSXsgetnP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r5b260_5b264.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Local Ltac lia := L5FastLia.plia.

Module PMSXG.
Import PMS.

(* [comment removed for export] *)
Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
  apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.
Ltac tr32 M0 AG := lazymatch goal with |- L5.u32_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u32_at sg M0 a v) by PMK.gmem;
  apply (PMF.u32_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Theorem xsgetn_ok : PMPSS.xsgetn_spec L HI.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"] (Mh_0185_blobs1.kr_b_360 ())). Qed.

End WithHeap.
End PMSXG.

End PnSrcSXsgetn.
From Stdlib Require ZArith List Lia Bool FunctionalExtensionality Permutation. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnTsWs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0261. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnTsWs2DP. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnTsWs2DA.
Module PnTsWs2DB.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnTsWs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0261. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnTsWs2DP PnTsWs2DA. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.PnHeapR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnTsSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197.PnTsWsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197.PnTsDivP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnTsWs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182.Ns0Opnew OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182.Ns0Opdel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r42d88_42d8c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r418a8_418ac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnTsSpecs12 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0025.PnTsWs2Math OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182.PnTsWs2Q OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197.PnTsWs2LP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0261.PnTsWs2L OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197.PnTsWs2HP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnTsWs2DP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0197.PnTsWs2DHP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnTsWs2DA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnTsWs2DB () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K69OSSVerify5KrLib7Mh_00846L5Defs2L56bstore02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00846L5Defs2L56bigobj01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56big_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB5XPostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST7tcreditC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnIface6debitRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01037PnHeapR4PMSR<debitR_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation03I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib7Sorting;Permutation?Permutation_symK47Corelib4Init5Logic3and01I46Stdlib5Lists4List5NoDup00C35stdpp4base?NoDup_ListNoDupC47Corelib5Lists7ListDef3mapC46Stdlib7Sorting;Permutation?Permutation_mapC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK:heap_nodupC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupC59OSSVerify5KrLib7Mh_00849HeapIface8hio_permC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Heap7HnIface4cszRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST;tcredit_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS7ts_textC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST7ws_postC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init9Datatypes4andbK69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS7WRS_SCRC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib9PnTsWs2DP8PQTSW2DP9land_byteC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib9PnTsWs2DP8PQTSW2DP8lor_byteC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z3oddC56Stdlib6ZArith6BinInt1Z=odd_add_mul_2C56Stdlib6ZArith6BinInt1Z8bit0_oddC46Stdlib4Bool4Bool;andb_true_rC46Stdlib4Bool4Bool<andb_false_rC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z8lor_specC59OSSVerify5KrLib9PnTsWs2DA8PQTSW2DA5dynfbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7testbitI47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool02C47Corelib4Init5Logic6eq_symc69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB6headDSC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB6headDMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB6headDLC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST6sh_dynC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST:ws_this_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST6ws_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST6ws_dynC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST3wsh01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST3wsh02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01859PnTsWs2DB8PQTSW2DB8ws_mainDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST9ws2d_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST6ws_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01069PnTsSpecs5PQTSS3WRSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0106;PnTsSpecs125PQTST3wsh00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00".

Module PQTSW2DB.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition TEN19 : Z := 10000000000000000000.
Local Ltac lia := L5FastLia.plia.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis OPNR : PMSR.opnewR_spec RSEGS AD L HI.
Hypothesis OPDR : PMSR.opdelR_spec RSEGS AD L HI.
Let KL := PMKS.klayout_S L LY.

Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o ot S r fb p v0 v1 : Z) (x : PM.vstr).
(* [comment removed for export] *)
Let LBp : list (Z * Z) := (p, 64) :: LB.
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LBp) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 ot.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S PQTSS.WRS_SCR.
Hypothesis BA0 : PMST.base_ok RSEGS AD M0.
Hypothesis THIS0 : L5.big_at RSEGS M0 o (L5.BO fb 2 (L5.BDyn 8 p)) /\ (fb = 1 \/ fb = 3) /\ p mod 16 = 0
                   /\ L5.u64_at RSEGS M0 p v0 /\ L5.u64_at RSEGS M0 (p + 8) v1 /\ 0 <= v0 < 2 ^ 64 /\ 1 <= v1 <= 2 ^ 30 /\ L5.defined M0 p 64.
Hypothesis O8 : o mod 8 = 0.
Hypothesis SO : S <= o.
Hypothesis OTOP : o + 32 <= hl_sptop L.
Hypothesis TB0 : PM.vstr_at RSEGS PMSP.T3 M0 ot x.
Hypothesis SZ0 : PM.vs_size x = 0.
Hypothesis TBM : match x with PM.VShort _ => True | PM.VLong c _ _ => 26 <= c end.
Hypothesis OT8 : ot mod 8 = 0.
Hypothesis SOT : S <= ot.
Hypothesis OTTOP : ot + 24 <= hl_sptop L.
Hypothesis DISJ : o + 32 <= ot \/ ot + 24 <= o.
Hypothesis CROK : PQTST.tcredit_pre L x 2 cr0.
Hypothesis CRD : 3 <= fst (PQTST.tcredit L x 2 cr0) /\ 3 * 2 ^ 20 <= snd (PQTST.tcredit L x 2 cr0).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr),
  regs_preserved R0 R' ->
  PM.vstr_at RSEGS PMSP.T3 M' ot x' -> 1 <= PM.vs_size x' <= 31 -> PQTSS.ts_text M' ot x' -> PQTST.ws_post L LBp M' 2 x x' ->
  L5C.hpres L LBp S PQTSS.WRS_SCR [(ot, 24)] M0 M' ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LBp) (PQTST.tcredit L x 2 cr0) M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

Lemma BRX : PMFR.brange L LBp.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_361 ())). Qed.
Lemma Hfb : 0 <= fb < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_362 ())). Qed.
Lemma Hv0 : 0 <= v0 < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_363 ())). Qed.
Lemma HV1 : 1 <= v1 <= 2 ^ 30.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_364 ())). Qed.

(* [comment removed for export] *)
Definition XPost (c q : Z) (cr1 : credit) : Prop :=
  cr1 = debitR (PQTST.tcredit L x 2 cr0) 64 /\
  match x with
  | PM.VShort _ => c = 48 /\ block_range L q 48 /\ blocks_apart q 48 LBp
  | PM.VLong c0 _ p0 => if (c0 <=? 44) then c = 48 /\ block_range L q 48 /\ blocks_apart q 48 LBp else c = c0 /\ q = p0
  end.
Lemma XPcr : forall c q cr1, XPost c q cr1 -> 2 <= fst cr1 /\ 2 * 2 ^ 20 <= snd cr1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_365 ())). Qed.

Let sv := PQTSW2L.sv R0.
Let sv_rng := PQTSW2L.sv_rng R0.
Let lregs := PQTSW2L.lregs R0 o ot S.
Let saved := PQTSW2L.saved R0 S.
Let mem_ok := PQTSW2L.mem_ok L M0 LBp ot S.
Let thisc := PQTSW2L.thisc o fb.
Let strL := PQTSW2L.strL L ot.
Let frame0 := PQTSW2L.frame0 L M0 o ot S STK0.
Let newR_call := PQTSW2DA.newR_call L HI LY HIok OPNR R0 M0 model0 K LBp o ot S MOK0 K0 Rtp0 STK0 BRX SO SOT.
Let delR_call := PQTSW2DA.delR_call L HI LY HIok OPDR R0 M0 model0 K LBp o ot S MOK0 K0 Rtp0 STK0 BRX SO SOT.
Let strL_call := PQTSW2DA.strL_call L M0 o ot S STK0 SOT OTTOP.
Let mem_ok_piece := PQTSW2L.mem_ok_piece L HI LY HIok M0 LBp o ot S STK0 BRX SO SOT.
Let strL_agree := PQTSW2L.strL_agree L M0 o ot S STK0 SOT OTTOP.
Let mem_ok_call := PQTSW2DA.mem_ok_call L HI LY HIok M0 LBp o ot S STK0 BRX SO SOT.
Let call_agree := PQTSW2DA.call_agree L LY M0 o ot S STK0 SO SOT.
Definition VX (pv : Z) := PQTSW2DA.VX S v0 v1 pv.
Let ctx (pv : Z) := PQTSW2L.ctx L HI R0 M0 model0 LBp [(pv, 64)] o ot S fb XPost.
Let tcells (pv : Z) := PQTSW2L.tcells S (VX pv).
Local Ltac wsfeed := first [ assumption | apply PQTSW2Q.zbv_u | apply PQTSW2Q.u_rng | PMK.rk | PMK.gmem | (cbv delta [PQTSW2HP.aligned PQTSW2DHP.aligned PQTSW2LP.aligned]; first [assumption | lia]) | PMK.sc ].
Local Ltac splits H := lazymatch type of H with _ /\ _ => let H1 := fresh "Cj" in let H2 := fresh "Cj" in destruct H as [H1 H2]; splits H1; splits H2 | _ => idtac end.
Local Ltac xfr1 M2 M3 AG bt H :=
  lazymatch type of H with
  | L5.u64_at _ M2 ?a ?v => apply (L5C.u64_at_agree RSEGS M2 M3 a v) in H; [| intros ii Hii; apply AG; revert Hii; bt | bt | bt]
  | L5.u32_at _ M2 ?a ?v => apply (PMF.u32_at_agree RSEGS M2 M3 a v) in H; [| intros ii Hii; apply AG; revert Hii; bt | bt | bt]
  | L5.u8_at _ M2 ?a ?v => apply (L5C.u8_at_agree RSEGS M2 M3 a v) in H; [| intros ii Hii; apply AG; revert Hii; bt | bt | bt]
  | L5.defined M2 ?a ?n => apply (L5C.defined_agree M2 M3 a n) in H; [| intros ii Hii; apply AG; revert Hii; bt]
  end.
Local Ltac xfrall M2 M3 AG1 AG2 AG3 bt :=
  repeat match goal with
  | H : L5.u64_at _ M2 _ _ |- _ => first [xfr1 M2 M3 AG1 bt H | xfr1 M2 M3 AG2 bt H | xfr1 M2 M3 AG3 bt H | clear H]
  | H : L5.u32_at _ M2 _ _ |- _ => first [xfr1 M2 M3 AG1 bt H | xfr1 M2 M3 AG2 bt H | xfr1 M2 M3 AG3 bt H | clear H]
  | H : L5.u8_at _ M2 _ _ |- _ => first [xfr1 M2 M3 AG1 bt H | xfr1 M2 M3 AG2 bt H | xfr1 M2 M3 AG3 bt H | clear H]
  | H : L5.defined M2 _ _ |- _ => first [xfr1 M2 M3 AG1 bt H | xfr1 M2 M3 AG2 bt H | xfr1 M2 M3 AG3 bt H | clear H]
  | H : L5.writable _ M2 _ _ |- _ => clear H
  | H : L5.img_clear M2 _ _ |- _ => clear H
  end.
(* [comment removed for export] *)
Lemma heap_swap2 x1 y1 l cr1 M1 VM : hi_heap HI (x1 :: y1 :: l) cr1 M1 VM -> hi_heap HI (y1 :: x1 :: l) cr1 M1 VM.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_366 ())). Qed.
(* [comment removed for export] *)
Lemma debit_debitR cr : debit L (debitR cr 64) 48 = debitR (debit L cr 48) 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_367 ())). Qed.
Lemma tcredit_le : fst (PQTST.tcredit L x 2 cr0) <= fst cr0 /\ snd (PQTST.tcredit L x 2 cr0) <= snd cr0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_368 ())). Qed.

(* [comment removed for export] *)
Lemma dynfb_ok j b : 0 <= j < 256 -> 0 <= b < 256 -> 0 <= PQTSW2DA.dynfb j b <= 255 /\ Z.testbit (PQTSW2DA.dynfb j b) 0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_369 ())). Qed.
Lemma finD (pv : Z) : 4096 <= pv /\ pv + 64 <= hl_ceil L /\ (pv + 64 <= hl_img_lo L \/ hl_img_hi L <= pv) ->
  PQTSW2L.fin_stmt L HI R0 M0 model0 K LBp [(pv, 64)] o ot S fb XPost (VX pv).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs1.kr_b_370 ())). Qed.
(* [comment removed for export] *)
Definition div1D (pv : Z) (HPV : 4096 <= pv /\ pv + 64 <= hl_ceil L /\ (pv + 64 <= hl_img_lo L \/ hl_img_hi L <= pv)) :=
  PQTSW2DA.div1D L HI LY HIok OPNR OPDR R0 M0 model0 K LBp o ot S fb v0 v1 pv XPost MOK0 K0 Rtp0 STK0 BRX Hfb O8 SO OTOP OT8 SOT OTTOP DISJ Hv0 HV1 HPV XPcr (finD pv HPV).

(* [comment removed for export] *)
Lemma headDL (c0 p0 : Z) : x = PM.VLong c0 0 p0 -> 45 <= c0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x46c40 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_371 ())). Qed.

(* [comment removed for export] *)
Lemma headDS : x = PM.VShort 0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x46c40 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_372 ())). Qed.

(* [comment removed for export] *)
Lemma headDM (c0 p0 : Z) : x = PM.VLong c0 0 p0 -> c0 <= 44 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x46c40 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_373 ())). Qed.

(* [comment removed for export] *)
Lemma ws_mainD : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x46c40 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_374 ())). Qed.

End Call.

Theorem ws2d_ok : PQTST.ws2d_spec L HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnTsWs2DB ()) ["WithHeap"] (Mh_0185_blobs2.kr_b_375 ())). Qed.

End WithHeap.
End PQTSW2DB.

End PnTsWs2DB.
From stdpp Require base list. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.
Module PnV8Span.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnParSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmTxtSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnCertKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnV8Kit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.PnV8Srd1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0182.PnV8SpanP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r41030_41034.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac2 kr_t_PnV8Span () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16sub_inC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC46Stdlib5Lists4List2InC46Stdlib5Lists4List:in_app_iffK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP3midC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6memrelC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6saves4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vw_oisC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01024PnV84PQV86v8_ownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8consumedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffI47Corelib4Init5Logic2or00C47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_osC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_ovC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic2or02C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_01067PnV8Kit5PQV8K6apart2C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4prod01C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib4Init5Logic7and_indC69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C47Corelib7Classes>Morphisms_Prop?or_iff_morphismK47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR12W0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP6inW_W0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP:outside_W0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP<base_ok_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vo_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_vp_issC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_strbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_classic_impC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM4sm_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_egC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_iss_iosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8zeros_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7iosb_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List9in_or_appK47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00905PgSrc3PGS7W_srcfGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib7Mh_01024PnV84PQV86pot_v8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01024PnV84PQV82v802C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vo_updC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<iss_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP9base_keepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I69OSSVerify5KrLib7Mh_01024PnV84PQV82v800C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K69OSSVerify5KrLib7Mh_01024PnV84PQV82v801C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGSAfill_buffer_specGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV8@srd_read_v_specGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV89vowner_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natc69OSSVerify5KrLib7Mh_01858PnV8Span5PQVSP8entry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV8Aread_span_v_specGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV86vowner00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~".
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQVSP.
Import PMS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Section Call.
Variables (V : PQV8.vowner) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (src0 : PM.srcst) (x0 : PQV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis VOK : PQV8.vowner_ok RSEGS AD L HI V.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 24576.
Hypothesis K0 : K [].
Hypothesis SPLO : S <= PQV8.vw_lo V.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNR0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis CRED0 : PMSP.credit_le (PQV8.pot_v8 L x0 g0) cr0.
Hypothesis FILL : PGS.fill_buffer_specG RSEGS AD L HI.
Hypothesis SRDV : PQV8.srd_read_v_specG RSEGS AD L HI 0x471f8.
#[local] Abbreviation os := (PQV8.vw_os V).
#[local] Abbreviation ois := (PQV8.vw_ois V).
#[local] Abbreviation ov := (PQV8.vw_ov V).
#[local] Abbreviation lo := (PQV8.vw_lo V).
#[local] Abbreviation hi := (PQV8.vw_hi V).
#[local] Abbreviation W0 := (PQVSR1.W0 V).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : PQV8.v8) (g' : Z)
            (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  PMSP.consumed src0 src' sm0 sm' = n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PQV8.v8_own x' ++ OB) ptr n) ->
  L5.defined M' ptr n ->
  PQV8.vw_at V M' src' x' g' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 6) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (PQV8.pot_v8 L x0 g0) (PQV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PQV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let LAYV : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= ov /\ ov + 24 <= hi /\ hi <= hl_sptop L /\ hi <= 2 ^ 47
           /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ ov mod 8 = 0 /\ 4096 <= lo
           /\ (os + 296 <= ois \/ ois + 272 <= os) /\ (ov + 24 <= os \/ os + 296 <= ov) /\ (ov + 24 <= ois \/ ois + 272 <= ov)
           /\ hl_ceil L <= lo /\ hl_errno L + 4 <= lo.
Proof. exact (PQV8.vo_lay _ _ _ _ V VOK). Qed.

Definition saves4 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))).
Definition kept8 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
Definition memrel (M : word -> option byte) : Prop :=
  PMK.ek L LBX S 24576 W0 M0 M /\ PMK.dk L LBX S 24576 M0 M /\ L5C.stk (hl_sptop L) M S 24576.
(* [comment removed for export] *)
Definition mid (M : word -> option byte) (src : PM.srcst) (sm : PM.strm) : Prop :=
  memrel M /\ saves4 M /\ PQV8.vw_at V M src x0 g0 OB /\ PM.iss_at RSEGS AD T3 M ois str sm /\ PMST.base_ok RSEGS AD M
  /\ hi_heap HI (PM.src_own src ++ PQV8.v8_own x0 ++ OB ++ LBX) cr0 M (m_vmmaps model0)
  /\ PMSP.consumed src0 src sm0 sm = 0 /\ PMSP.src_step src0 src sm0 sm.
Definition rregs (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 32) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 os /\ getr R (reg 18) = Z_to_bv 64 ov /\ kept8 R.

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_376 ())). Qed.
Ltac kept_tac KS KP := intros j Hj; rewrite (KS j) by (revert j Hj; apply sub_in; vm_compute; reflexivity); apply KP; exact Hj.
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma own_facts M src sm : mid M src sm ->
  forall B m, In (B, m) (PM.src_own src ++ PQV8.v8_own x0 ++ OB) -> 4096 <= B /\ B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\
    forall B' m', In (B', m') LBX -> B + m <= B' \/ B' + m' <= B.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_377 ())). Qed.
Lemma inW_W0 a : PMK.inW W0 a -> lo <= a < hi.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_378 ())). Qed.
Lemma outside_W0 a : a < lo -> L5.outside W0 a.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_379 ())). Qed.
Lemma base_keep M M' : PMK.ek L LBX S 24576 W0 M M' -> L5C.stk (hl_sptop L) M S 24576 -> PMST.base_ok RSEGS AD M -> PMST.base_ok RSEGS AD M'.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_380 ())). Qed.
Lemma src_facts M src sm : mid M src sm ->
  0 <= PM.unread src sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem src <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm
  /\ PM.sr_qc src <= PM.sr_de src /\ PM.sr_de src + PM.sr_rem src <= PM.sr_qc src + PM.CHUNK.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_381 ())). Qed.

(* [comment removed for export] *)
Lemma src_upd M M1 src src1 sm :
  memrel M -> PQV8.vw_at V M src x0 g0 OB -> PM.iss_at RSEGS AD T3 M ois str sm -> PMST.base_ok RSEGS AD M ->
  hi_heap HI (PM.src_own src ++ PQV8.v8_own x0 ++ OB ++ LBX) cr0 M (m_vmmaps model0) -> mem_grows M M1 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (os + 256 <= i < os + 296) -> ~ (S - 32 <= i < S) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  PM.src_fields_at RSEGS T3 M1 os ois (ois + 16) src1 -> PM.sr_qc src1 = PM.sr_qc src ->
  memrel M1 /\ PQV8.vw_at V M1 src1 x0 g0 OB /\ PM.iss_at RSEGS AD T3 M1 ois str sm /\ PMST.base_ok RSEGS AD M1.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_382 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FASTK (fx : FPState) R M src sm :
  rregs R -> getr R (reg 11) = Z_to_bv 64 (PM.sr_rem src) -> 1 <= len <= PM.sr_rem src -> mid M src sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x46834 M model0) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_383 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma SLOWK (fx : FPState) R M src sm :
  rregs R -> 1 <= len -> mid M src sm -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x46880 M model0) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_384 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma R0K (fx : FPState) R M src sm :
  rregs R -> 1 <= len -> PM.sr_rem src = 0 -> mid M src sm -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x46858 M model0) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_385 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_ok (fx : FPState) :
  hi_heap HI (PM.src_own src0 ++ PQV8.v8_own x0 ++ OB ++ LBX) cr0 M0 (m_vmmaps model0) ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 len -> getr R0 (reg 12) = Z_to_bv 64 ov ->
  PQV8.vw_at V M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD T3 M0 ois str sm0 -> PMST.base_ok RSEGS AD M0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x46804 M0 model0) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_386 ())). Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem read_span_v_ok :
  PGS.fill_buffer_specG RSEGS AD L HI -> PQV8.srd_read_v_specG RSEGS AD L HI 0x471f8 -> PQV8.read_span_v_specG RSEGS AD L HI 0x46804.
Proof.
ltac2:(KReplay.run1 (kr_t_PnV8Span ()) ["WithHeap"] (Mh_0185_blobs2.kr_b_387 ())). Qed.

End WithHeap.
End PQVSP.

End PnV8Span.
Module PnV8Srd5.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnParSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmTxtSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnCertKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0103.PnSrcGW OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0106.PnV8Kit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.PnV8SrdP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r42098_4209c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.PnV8Srd1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.PnV8Srd2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.PnV8Srd3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0193.PnV8Srd4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac2 kr_t_PnV8Srd5 () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3appI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC47Corelib4Init5Logic3notK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C47Corelib4Init5Logic8eq_transK47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_00907PmModel2PM6mu_srcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Peano2ltC69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16lstateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR15lregsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR18state_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR14acctC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR19unread_nnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM4sm_gC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_egC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR13IHtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Srd56PQVSR54headC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV82v800C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2InC46Stdlib5Lists4List:in_app_iffI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86v8_ownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vw_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86pot_v8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85vw_ovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR12W0C1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyK47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;brange_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vo_srcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16memrelC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC46Stdlib5Lists4List=Forall_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocK47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_01067PnV8Kit5PQV8K6apart2C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00905PgSrc3PGS7W_srcfGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC47Corelib4Init5Logic7and_indC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8consumedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV87v8_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV85v8_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01024PnV84PQV82v802C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV86vo_updC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<iss_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR19base_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_ReflexiveI47Corelib4Init5Logic2ex00K69OSSVerify5KrLib7Mh_01024PnV84PQV82v801C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP8svA_concC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallc69OSSVerify5KrLib7Mh_01858PnV8Srd56PQVSR5;entry_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16saves8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR15kept7C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01938PnV8Srd16PQVSR16sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Srd56PQVSR54loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP8KS_svA_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01938PnV8SrdP6PQVSRP8KS_svA_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r42098_4209c7W_472ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r42098_4209c7F_472ecC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0020ENs0_code_r42098_4209c7D_472ecC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV8?vu8_resize_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS>src_read_specGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01037PnSrcGW4PQSWEfill_buffer_win_specGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV89vowner_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01858PnV8Srd56PQVSR58entry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01024PnV84PQV8@srd_read_v_specGC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01024PnV84PQV86vowner00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~".
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQVSR5.
Import PMS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.

Lemma u8_of_u32 (segs : list Segment) (M : word -> option byte) a w : 0 <= w < 2 ^ 32 -> L5.u32_at segs M a w -> L5.u8_at segs M a (w mod 256).
Proof.
ltac2:(KReplay.run1 (kr_t_PnV8Srd5 ()) [] (Mh_0185_blobs2.kr_b_388 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.

Section Call.
Variables (V : PQV8.vowner) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (OB LBX : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (src0 : PM.srcst) (x0 : PQV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
Hypothesis VOK : PQV8.vowner_ok RSEGS AD L HI V.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 22528.
Hypothesis K0 : K [].
Hypothesis SPLO : S <= PQV8.vw_lo V.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNR0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis VRES : PQV8.vu8_resize_spec RSEGS AD L HI 0x47338.
Hypothesis SRD : PGS.src_read_specG RSEGS AD L HI.
Hypothesis FBW : PQSW.fill_buffer_win_specG RSEGS AD L HI.
#[local] Abbreviation os := (PQV8.vw_os V).
#[local] Abbreviation ois := (PQV8.vw_ois V).
#[local] Abbreviation ov := (PQV8.vw_ov V).
#[local] Abbreviation lo := (PQV8.vw_lo V).
#[local] Abbreviation hi := (PQV8.vw_hi V).
#[local] Abbreviation W0 := (PQVSR1.W0 V).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (src' : PM.srcst) (x' : PQV8.v8) (g' : Z)
                         (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PQV8.v8_size x' = d ->
  PQV8.vw_at V M' src' x' g' OB -> PM.iss_at RSEGS AD T3 M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5C.hpres L LBX S (PMSP.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (PQV8.pot_v8 L x0 g0) (PQV8.pot_v8 L x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.src_own src' ++ PQV8.v8_own x' ++ OB ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation saves8 := (PQVSR1.saves8 R0 S).
#[local] Abbreviation kept7 := (PQVSR1.kept7 R0).
#[local] Abbreviation memrel := (PQVSR1.memrel L V M0 LBX S).
#[local] Abbreviation acct := (PQVSR1.acct len src0 sm0).
#[local] Abbreviation state_ok := (PQVSR1.state_ok L HI V R0 M0 model0 OB LBX cr0 S x0 g0 str).
#[local] Abbreviation lregs := (PQVSR1.lregs V R0 S len).
#[local] Abbreviation lstate := (PQVSR1.lstate L HI V R0 M0 model0 OB LBX cr0 S len src0 x0 g0 str sm0).
#[local] Abbreviation IHt := (PQVSR1.IHt L HI V R0 M0 model0 K OB LBX cr0 S len src0 x0 g0 str sm0).
#[local] Abbreviation finish := (PQVSR1.finish L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).
#[local] Abbreviation unread_nn := (PQVSR1.unread_nn L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).
#[local] Abbreviation own_facts := (PQVSR1.own_facts L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).
#[local] Abbreviation base_keep := (PQVSR1.base_keep L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).
#[local] Abbreviation vec_facts := (PQVSR2.vec_facts L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).
#[local] Abbreviation rpath := (PQVSR3.rpath L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).
#[local] Abbreviation dpath := (PQVSR4.dpath L HI LY HIok V R0 M0 model0 K OB LBX cr0 S r len src0 x0 g0 str sm0 VOK Rra0 RAok Rsp0 Rgp0 Rtp0 STK0 K0 SPLO Hlen INCS UNR0 VRES SRD FBW KONT).

Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat.
Ltac ksr KS k H := rewrite (KS k) by PMK.inl; exact H.
Ltac kept_tac KS KP := intros j Hj; rewrite (KS j) by (revert j Hj; apply PQVSR1.sub_in; vm_compute; reflexivity); apply KP; exact Hj.

Let LAYV : lo <= os /\ os + 296 <= hi /\ lo <= ois /\ ois + 272 <= hi /\ lo <= ov /\ ov + 24 <= hi /\ hi <= hl_sptop L /\ hi <= 2 ^ 47
           /\ os mod 8 = 0 /\ ois mod 8 = 0 /\ ov mod 8 = 0 /\ 4096 <= lo
           /\ (os + 296 <= ois \/ ois + 272 <= os) /\ (ov + 24 <= os \/ os + 296 <= ov) /\ (ov + 24 <= ois \/ ois + 272 <= ov)
           /\ hl_ceil L <= lo /\ hl_errno L + 4 <= lo.
Proof. exact (PQV8.vo_lay _ _ _ _ V VOK). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma head mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr (w : Z) :
  lstate R M model src x g sm cr w -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x47230 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_tL_Mh_0185 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_389 ())). Qed.

(* [comment removed for export] *)
Lemma loop (n : nat) : forall (fx : FPState) R M model src x g sm cr w,
  (Z.to_nat (PM.mu_src src sm) < n)%nat -> lstate R M model src x g sm cr w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x47230 M model) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Srd5 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_390 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_state (fx : FPState) M1 :
  hi_heap HI (PM.src_own src0 ++ PQV8.v8_own x0 ++ OB ++ LBX) cr0 M0 (m_vmmaps model0) -> PMSP.model_ok model0 ->
  PQV8.vw_at V M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD T3 M0 ois str sm0 -> PMST.base_ok RSEGS AD M0 ->
  PMSP.credit_le (PQV8.pot_v8 L x0 g0) cr0 ->
  mem_grows M0 M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 64 <= i < S - 64 + 64) -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)) ->
  PQVSR1.memrel L V M0 LBX S M1 /\ PQV8.vw_at V M1 src0 x0 g0 OB /\ PM.iss_at RSEGS AD T3 M1 ois str sm0 /\ PMST.base_ok RSEGS AD M1.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Srd5 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_391 ())). Qed.

(* [comment removed for export] *)
Lemma entry_ok (fx : FPState) :
  hi_heap HI (PM.src_own src0 ++ PQV8.v8_own x0 ++ OB ++ LBX) cr0 M0 (m_vmmaps model0) -> PMSP.model_ok model0 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 ov -> getr R0 (reg 12) = Z_to_bv 64 len ->
  PQV8.vw_at V M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD T3 M0 ois str sm0 -> PMST.base_ok RSEGS AD M0 ->
  PQV8.v8_size x0 = 0 -> PMSP.credit_le (PQV8.pot_v8 L x0 g0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x471f8 M0 model0) K.
Proof using All.
ltac2:(KReplay.run1 (kr_t_PnV8Srd5 ()) ["WithHeap"; "Call"] (Mh_0185_blobs2.kr_b_392 ())). Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem srd_read_v_ok :
  PQV8.vu8_resize_spec RSEGS AD L HI 0x47338 -> PGS.src_read_specG RSEGS AD L HI -> PQSW.fill_buffer_win_specG RSEGS AD L HI ->
  PQV8.srd_read_v_specG RSEGS AD L HI 0x471f8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnV8Srd5 ()) ["WithHeap"] (Mh_0185_blobs2.kr_b_393 ())). Qed.

End WithHeap.
End PQVSR5.

End PnV8Srd5.
