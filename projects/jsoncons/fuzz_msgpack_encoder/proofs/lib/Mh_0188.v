(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0188_blobs1.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module PnAdSGbP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSGbP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEs_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEs_1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEs3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP?KS_ad_gbEs_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP?KS_ad_gbEs_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEl_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEl_1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbEl3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP?KS_ad_gbEl_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP?KS_ad_gbEl_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP9KS_ad_gbRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbR3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbR_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;KS_ad_gbN_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;KS_ad_gbN_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP>KS_ad_gbN_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbN6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP>KS_ad_gbN_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP:KS_ad_gbTsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs<seg_sound_axC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTs3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP=KS_ad_gbTs_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP:KS_ad_gbTdC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP8Pad_gbTd3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP=KS_ad_gbTd_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP9KS_ad_gbFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7Pad_gbF3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbF_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADGBP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_004 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_005 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_006 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_007 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_008 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_009 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_010 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_011 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_012 ())). Qed.
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
Module Pad_gbEs := BndP_Ns_030.LibSegNs_ad_gbEs.
Definition KS_ad_gbEs_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbEs.regs0 Pad_gbEs.regs_out0).
Lemma KS_ad_gbEs_0_ok : BG.kept_ok 64 Pad_gbEs.regs0 Pad_gbEs.regs_out0 KS_ad_gbEs_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_013 ())). Qed.
Definition KS_ad_gbEs_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbEs.regs0 Pad_gbEs.regs_out1).
Lemma KS_ad_gbEs_1_ok : BG.kept_ok 64 Pad_gbEs.regs0 Pad_gbEs.regs_out1 KS_ad_gbEs_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_014 ())). Qed.
Lemma ad_gbEs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 22 -> getr R (reg 12) = Z_to_bv 64 ((V 34%nat) - 22) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 80)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (2 * (V 35%nat)) ->
  0 <= (V 35%nat) <= 22 -> 0 <= (Z.land ((2 * (V 35%nat)) mod 2 ^ 64) 1) <= 0 -> 23 <= (V 34%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x662f8 M) (st fx' R' 0x6638c M')
        /\ (forall x, In x KS_ad_gbEs_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 22
        /\ getr R' (reg 10) = Z_to_bv 64 44
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551585
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = getr R (reg 16)
        /\ getr R' (reg 19) = getr R (reg 15)
        /\ getr R' (reg 20) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ getr R' (reg 22) = getr R (reg 13)
        /\ 44 < (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x662f8 M) (st fx' R' 0x6638c M')
        /\ (forall x, In x KS_ad_gbEs_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 22
        /\ getr R' (reg 10) = Z_to_bv 64 44
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551585
        /\ getr R' (reg 12) = Z_to_bv 64 44
        /\ getr R' (reg 18) = getr R (reg 16)
        /\ getr R' (reg 19) = getr R (reg 15)
        /\ getr R' (reg 20) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ getr R' (reg 22) = getr R (reg 13)
        /\ (V 34%nat) <= 44
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_015 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_gbEl := BndP_Ns_030.LibSegNs_ad_gbEl.
Definition KS_ad_gbEl_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbEl.regs0 Pad_gbEl.regs_out0).
Lemma KS_ad_gbEl_0_ok : BG.kept_ok 64 Pad_gbEl.regs0 Pad_gbEl.regs_out0 KS_ad_gbEl_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_016 ())). Qed.
Definition KS_ad_gbEl_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbEl.regs0 Pad_gbEl.regs_out1).
Lemma KS_ad_gbEl_1_ok : BG.kept_ok 64 Pad_gbEl.regs0 Pad_gbEl.regs_out1 KS_ad_gbEl_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_017 ())). Qed.
Lemma ad_gbEl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 38%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 34%nat) - (V 38%nat)) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 80)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 37%nat) -> 25 <= (V 38%nat) <= 2147483648 ->
  26 <= (V 34%nat) <= 1073741824 -> 1 <= ((V 34%nat) - (V 38%nat)) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x662f8 M) (st fx' R' 0x6638c M')
        /\ (forall x, In x KS_ad_gbEl_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * (V 38%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 38%nat)) - 9)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = getr R (reg 16)
        /\ getr R' (reg 19) = getr R (reg 15)
        /\ getr R' (reg 20) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 22) = getr R (reg 13)
        /\ ((2 * (V 38%nat)) mod 2 ^ 64) < (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x662f8 M) (st fx' R' 0x6638c M')
        /\ (forall x, In x KS_ad_gbEl_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * (V 38%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 38%nat)) - 9)
        /\ getr R' (reg 12) = Z_to_bv 64 (2 * (V 38%nat))
        /\ getr R' (reg 18) = getr R (reg 16)
        /\ getr R' (reg 19) = getr R (reg 15)
        /\ getr R' (reg 20) = getr R (reg 14)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 22) = getr R (reg 13)
        /\ (V 34%nat) <= ((2 * (V 38%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_018 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_gbR := BndP_Ns_030.LibSegNs_ad_gbR.
Definition KS_ad_gbR : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbR.regs0 Pad_gbR.regs_out0).
Lemma KS_ad_gbR_ok : BG.kept_ok 64 Pad_gbR.regs0 Pad_gbR.regs_out0 KS_ad_gbR = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_019 ())). Qed.
Lemma ad_gbR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 44 <= (V 36%nat) <= 2147483648 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6638c M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_ad_gbR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418744
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * ((V 36%nat) / 8)) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 ((8 * ((V 36%nat) / 8)) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_020 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_gbN := BndP_Ns_030.LibSegNs_ad_gbN.
Definition KS_ad_gbN_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbN.regs0 Pad_gbN.regs_out0).
Lemma KS_ad_gbN_0_ok : BG.kept_ok 64 Pad_gbN.regs0 Pad_gbN.regs_out0 KS_ad_gbN_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_021 ())). Qed.
Definition KS_ad_gbN_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbN.regs0 Pad_gbN.regs_out1).
Lemma KS_ad_gbN_1_ok : BG.kept_ok 64 Pad_gbN.regs0 Pad_gbN.regs_out1 KS_ad_gbN_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_022 ())). Qed.
Lemma ad_gbN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 0 <= (V 35%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x663b8 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_gbN_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418768
        /\ getr R' (reg 11) = getr R (reg 21)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 24) = getr R (reg 10)
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x663b8 M) (st fx' R' 0x663d0 M')
        /\ (forall x, In x KS_ad_gbN_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 24) = getr R (reg 10)
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_023 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_gbTs := BndP_Ns_030.LibSegNs_ad_gbTs.
Definition KS_ad_gbTs : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbTs.regs0 Pad_gbTs.regs_out0).
Lemma KS_ad_gbTs_ok : BG.kept_ok 64 Pad_gbTs.regs0 Pad_gbTs.regs_out0 KS_ad_gbTs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_024 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ad_gbTs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 22 -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 (V 35%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (bv_unsigned (getr R (reg 8))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 8))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 8))) \/ (bv_unsigned (getr R (reg 8))) + 24 <= ((V 2%nat) - 80)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 8))) 24 -> 0 <= (V 35%nat) <= 22 ->
  48 <= (bv_unsigned (getr R (reg 23))) <= 2147483648 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 49%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((bv_unsigned (getr R (reg 8))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 8))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((bv_unsigned (getr R (reg 8))) + 0) <= i < ((bv_unsigned (getr R (reg 8))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x663d0 M) (st fx' R' 0x6643c M')
        /\ (forall x, In x KS_ad_gbTs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((2 * ((bv_unsigned (getr R (reg 23))) / 2)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 23
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 8))) + 16) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 8))) ((2 * ((bv_unsigned (getr R (reg 23))) / 2)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 49%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_025 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_gbTd := BndP_Ns_030.LibSegNs_ad_gbTd.
Definition KS_ad_gbTd : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbTd.regs0 Pad_gbTd.regs_out0).
Lemma KS_ad_gbTd_ok : BG.kept_ok 64 Pad_gbTd.regs0 Pad_gbTd.regs_out0 KS_ad_gbTd = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_026 ())). Qed.
Lemma ad_gbTd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 22) = Z_to_bv 64 (V 35%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 25 <= (bv_unsigned (getr R (reg 9))) <= 2147483648 ->
  0 <= (V 35%nat) <= 2147483648 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x663d0 M) (st fx' R' 0x63dc4 M')
        /\ (forall x, In x KS_ad_gbTd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 418820
        /\ getr R' (reg 10) = getr R (reg 21)
        /\ getr R' (reg 11) = Z_to_bv 64 ((bv_unsigned (getr R (reg 9))) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_027 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_gbF := BndP_Ns_030.LibSegNs_ad_gbF.
Definition KS_ad_gbF : list nat := Eval vm_compute in (BG.kept_list 64 Pad_gbF.regs0 Pad_gbF.regs_out0).
Lemma KS_ad_gbF_ok : BG.kept_ok 64 Pad_gbF.regs0 Pad_gbF.regs_out0 KS_ad_gbF = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_028 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ad_gbF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483152 <= (bv_unsigned (getr R (reg 8))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 8))) 8 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 8))) \/ (bv_unsigned (getr R (reg 8))) + 24 <= ((V 2%nat) - 80)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 8))) 24 -> 48 <= (bv_unsigned (getr R (reg 23))) <= 2147483648 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 49%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((bv_unsigned (getr R (reg 8))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 8))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((bv_unsigned (getr R (reg 8))) + 0) <= i < ((bv_unsigned (getr R (reg 8))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66404 M) (st fx' R' 0x6643c M')
        /\ (forall x, In x KS_ad_gbF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((2 * ((bv_unsigned (getr R (reg 23))) / 2)) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 8))) + 16) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 8))) ((2 * ((bv_unsigned (getr R (reg 23))) / 2)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 49%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbP ()) [] (Mh_0188_blobs1.kr_b_029 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

End PQADGBP.

End PnAdSGbP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LeanFeed2. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. From stdpp Require base list. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0188 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega7EnvRing5PExpr00K47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega5Tauto8GFormula00C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07I46Stdlib9micromega7EnvRing3Pol00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divc69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppK47Corelib4Init9Datatypes6option02C46Stdlib5Lists4List7forallbC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extI46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaI47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC35stdpp7tactics<f_equal_helpC45stdpp9bitvector;definitions;bv_unsignedc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6mem_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C56Stdlib6ZArith6BinInt1Z7testbitC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5reg_uC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=testbit_odd_0c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_isL_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS<mem_ok_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS=kstr_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS4cndLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6sub_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS:src_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6tail_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS9grow_callC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isL_1C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isL_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5src_qC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5sz_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6mem_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5reg_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jsL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS4cndLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5savesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS9grow_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsL_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsL_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5src_qC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5sz_SMC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6mem_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC5savesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangec69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbLI_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7kc_snocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC3finC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbLIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC3KCFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6frame0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC3BRXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC5reg_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbF_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbFC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC8cnd_evalC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbL0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6cnd_neC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7tail_LIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6cnd_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6grow_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbL0_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbL0_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7mem_ok0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z9mod_smallc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbEl_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC;bytes_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6mem_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC5savesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC4growC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEl_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEl_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6GB_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC3KCFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7mem_ok0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landc69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6mem_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5reg_uC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2>u64_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2<u64_low_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>testbit_even_0c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_isS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC7land2_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC<mem_ok_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC4cndSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5savesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6tail_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC9grow_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC3KCFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5src_qC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5sz_SMC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isS_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC4cndLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6mem_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5reg_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jsS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC7land2_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC4cndSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5savesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6tail_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC9grow_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC3KCFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5src_qC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5sz_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsS_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC4cndLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jwL_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rc69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC8ret_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6safe_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC7mem_ok0C1?~~~~~~~~~~~~~~~".
Module PnAdSGb.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGbP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r62758_6275c.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSGb () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6GB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ks_growC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6cap_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9gcount_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3divc69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB3BRXC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR7inW_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR<defined_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR5ag_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB=kstr_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPNEW_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB8growth_BC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6growthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62758_6275c7W_663f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62758_6275c7F_663f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62758_6275c7D_663f4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB5reg_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;ad_gbF_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB<mem_ok_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6cs_finC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP9KS_ad_gbFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbTs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP:KS_ad_gbTsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbTd_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opdel_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB<saves_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB=mem_ok_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6tail_FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP:KS_ad_gbTdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7tail_TsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7tail_TdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7x_casesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;ad_gbN_concC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C56Stdlib6ZArith6BinInt1Z7sub_0_rC69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove5PMCPS;memmove_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB;saves_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6at_648C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;KS_ad_gbN_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;KS_ad_gbN_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB;size_le_capC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;ad_gbR_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS;pot_ks_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7stk_newC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS<opnew_spec_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;fresh_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBfresh_block_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB;kstr_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C?blocks_apart_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB9after_newC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP9KS_ad_gbRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB8alloc_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB4A_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS4NREQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbEs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7land2_0C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB4growC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEs_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEs_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7mem_ok0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbEl_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEl_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEl_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7entry_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7entry_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7gb_mainC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7gb_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADGB.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) [] (Mh_0188_blobs1.kr_b_030 ())). Qed.

Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) [] (Mh_0188_blobs1.kr_b_031 ())). Qed.

Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) [] (Mh_0188_blobs1.kr_b_032 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_at_agree (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> L5C.agree_on M M' o 24 -> (forall c n p, x = PM.VLong c n p -> L5C.agree_on M M' p c) ->
  kstr_at M o x -> kstr_at M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) [] (Mh_0188_blobs1.kr_b_033 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.

(* [comment removed for export] *)
Definition GB_SCR : Z := 14272.

(* [comment removed for export] *)
Definition gb_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o need sp r SM g : Z) (x : PM.vstr),
    hi_heap HI (PM.vs_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp AD) ->
    L5C.stk (hl_sptop L) M sp GB_SCR ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 (PM.vs_cap x) -> getr R 12%bv = Z_to_bv 64 (need - PM.vs_cap x) ->
    getr R 13%bv = Z_to_bv 64 (PM.vs_size x) -> getr R 14%bv = Z_to_bv 64 (PM.vs_size x) -> getr R 15%bv = Z_to_bv 64 0 ->
    kstr_at M o x -> PQM.ks_ok SM x g -> SM <= PQAS.SMMAX -> PM.vs_cap x < need <= SM ->
    sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    PMSP.credit_le (PQM.pot_ks L SM x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B A : Z) (cr' : credit),
        regs_preserved R R' -> A = PQAS.gcount (PM.vs_cap x) need ->
        L5.defined M' o 24 -> L5.u64_at RSEGS M' o (A + 1) -> L5.u64_at RSEGS M' (o + 16) B ->
        L5.defined M' B A -> 4096 <= B -> B + A <= hl_ceil L ->
        PQM.ks_ok SM (PM.VLong A need B) (g + 1) -> need < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
        L5C.hpres L LB sp GB_SCR [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
        model_but_vm model model' -> hi_heap HI ((B, A) :: LB) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o need S r SM g : Z) (x : PM.vstr).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S GB_SCR.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (PM.vs_cap x).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 (need - PM.vs_cap x).
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 (PM.vs_size x).
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 (PM.vs_size x).
Hypothesis A15 : getr R0 (reg 15) = Z_to_bv 64 0.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis Hneed : PM.vs_cap x < need <= SM.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B A : Z) (cr' : credit),
  regs_preserved R0 R' -> A = PQAS.gcount (PM.vs_cap x) need ->
  L5.defined M' o 24 -> L5.u64_at RSEGS M' o (A + 1) -> L5.u64_at RSEGS M' (o + 16) B ->
  L5.defined M' B A -> 4096 <= B -> B + A <= hl_ceil L ->
  PQM.ks_ok SM (PM.VLong A need B) (g + 1) -> need < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
  L5C.hpres L LB S GB_SCR [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  model_but_vm model0 model' -> hi_heap HI ((B, A) :: LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let A : Z := PQAS.gcount (PM.vs_cap x) need.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S GB_SCR [(o, 24)] M0 M /\ PMK.dk L LB S GB_SCR M0 M /\ L5C.stk (hl_sptop L) M S GB_SCR /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_034 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_035 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14272 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14272 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_036 ())). Qed.

(* [comment removed for export] *)
Lemma cap_ge : 22 <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_037 ())). Qed.
Lemma size_le_cap : 0 <= PM.vs_size x <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_038 ())). Qed.
Lemma growth : PQM.ks_ok SM (PM.VLong A need 0) (g + 1) /\ 2 * PQM.ks_alloc x <= A /\ 48 <= A /\ A <= 2 * SM + 8 /\ A mod 8 = 0
               /\ need < A /\ 26 <= A <= PQM.KCAP /\ A mod 2 = 0 /\ g < PQM.GMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_039 ())). Qed.
Lemma growth_B B : PQM.ks_ok SM (PM.VLong A need B) (g + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_040 ())). Qed.
Lemma alloc_le : PQM.ks_alloc x <= SM.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_041 ())). Qed.
Lemma A_eq : A = 8 * (Z.max (2 * PM.vs_cap x) need / 8) + 8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_042 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 80 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_043 ())). Qed.

Lemma mem_ok_callee M1 M3 LBc scr :
  mem_ok M1 -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> incl LB LBc -> PMFR.brange L LBc -> 0 <= scr -> 80 + scr <= GB_SCR ->
  L5C.stk (hl_sptop L) M1 (S - 80) scr -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_044 ())). Qed.

Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 80 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_045 ())). Qed.

Lemma saves_callee M1 M3 LBc scr :
  saves M1 -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> 0 <= scr -> L5C.stk (hl_sptop L) M1 (S - 80) scr -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_046 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_callee M1 M3 LBc scr :
  kstr_at M1 o x -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> incl (PM.vs_own x) LBc -> PMFR.brange L LBc -> 0 <= scr ->
  L5C.stk (hl_sptop L) M1 (S - 80) scr -> kstr_at M3 o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_047 ())). Qed.

Lemma stk_new M1 : mem_ok M1 -> L5C.stk (hl_sptop L) M1 (S - 80) PMSP.OPNEW_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_048 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  L5.u64_at RSEGS M1 o (A + 1) -> L5.u64_at RSEGS M1 (o + 16) B -> L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L ->
  mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) -> model_but_vm model0 model1 ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x6643c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_049 ())). Qed.

(* [comment removed for export] *)
Lemma cs_fin (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S ->
  getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R1 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) ->
  getr R1 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) ->
  (forall k, In k [3; 4; 25; 26; 27]%nat -> getr R1 (reg k) = getr R0 (reg k)) ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_050 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_F (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 23) = Z_to_bv 64 A -> getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66404 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_051 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_Ts (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (n0 B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VShort n0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 22 -> getr R1 (reg 19) = Z_to_bv 64 0 ->
  getr R1 (reg 20) = Z_to_bv 64 n0 -> getr R1 (reg 22) = Z_to_bv 64 n0 -> getr R1 (reg 23) = Z_to_bv 64 A -> getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663d0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_052 ())). Qed.

(* [comment removed for export] *)
Lemma tail_Td (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c n p B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VLong c n p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (c - 1) -> getr R1 (reg 19) = Z_to_bv 64 0 ->
  getr R1 (reg 20) = Z_to_bv 64 n -> getr R1 (reg 21) = Z_to_bv 64 p -> getr R1 (reg 22) = Z_to_bv 64 n -> getr R1 (reg 23) = Z_to_bv 64 A ->
  getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> B <> p ->
  hi_heap HI ((B, A) :: (p, c) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663d0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_053 ())). Qed.

(* [comment removed for export] *)
Lemma x_cases : (exists n0, x = PM.VShort n0) \/ (exists c n p, x = PM.VLong c n p).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_054 ())). Qed.

Lemma at_648 (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (PM.vs_cap x) -> getr R1 (reg 19) = Z_to_bv 64 0 ->
  getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 21) = Z_to_bv 64 (PM.vs_data o x) -> getr R1 (reg 22) = Z_to_bv 64 (PM.vs_size x) ->
  getr R1 (reg 23) = Z_to_bv 64 A -> getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> (forall c n p, x = PM.VLong c n p -> B <> p) ->
  hi_heap HI ((B, A) :: PM.vs_own x ++ LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663d0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_055 ())). Qed.

(* [comment removed for export] *)
Lemma after_new (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (PM.vs_cap x) -> getr R1 (reg 10) = Z_to_bv 64 B ->
  getr R1 (reg 19) = Z_to_bv 64 0 -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 21) = Z_to_bv 64 (PM.vs_data o x) ->
  getr R1 (reg 22) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 23) = Z_to_bv 64 A ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> (forall c n p, x = PM.VLong c n p -> B + A <= p \/ p + c <= B) ->
  hi_heap HI ((B, A) :: PM.vs_own x ++ LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663b8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_056 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (PM.vs_cap x) ->
  getr R1 (reg 12) = Z_to_bv 64 (Z.max (2 * PM.vs_cap x) need) -> getr R1 (reg 19) = Z_to_bv 64 0 -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) ->
  getr R1 (reg 21) = Z_to_bv 64 (PM.vs_data o x) -> getr R1 (reg 22) = Z_to_bv 64 (PM.vs_size x) ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x6638c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_057 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_S (n0 : Z) : x = PM.VShort n0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x662f8 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_058 ())). Qed.

(* [comment removed for export] *)
Lemma entry_L (c n p : Z) : x = PM.VLong c n p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x662f8 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_059 ())). Qed.

(* [comment removed for export] *)
Lemma gb_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x662f8 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_060 ())). Qed.

End Call.

Theorem gb_ok : gb_spec 0x662f8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGb ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_061 ())). Qed.

End WithHeap.
End PQADGB.

End PnAdSGb.
Module PnAdSInsP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSInsP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS9regs_out3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwS_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwS_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwS_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS6cells3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwS3ps3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwS_3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL9regs_out3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwL_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwL_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwL_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL6cells3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_iwL3ps3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_iwL_3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isS_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isS_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS6cells0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isS3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_isS_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_isS_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isL_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isL_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isL3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_isL_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP>KS_ad_isL_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP9KS_ad_isGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<KS_ad_isG_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7Pad_isG6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isTsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP=KS_ad_isTs_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTs6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isTlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP=KS_ad_isTl_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isTl6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isRsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRs3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP=KS_ad_isRs_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isRlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP8Pad_isRl3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP=KS_ad_isRl_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADINSP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_062 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_063 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_064 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_065 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_066 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_067 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_068 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_069 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_070 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_071 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_072 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_073 ())). Qed.
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
Module Pad_iwS := BndP_Ns_033.LibSegNs_ad_iwS.
Definition KS_ad_iwS_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwS.regs0 Pad_iwS.regs_out0).
Lemma KS_ad_iwS_0_ok : BG.kept_ok 64 Pad_iwS.regs0 Pad_iwS.regs_out0 KS_ad_iwS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_074 ())). Qed.
Definition KS_ad_iwS_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwS.regs0 Pad_iwS.regs_out1).
Lemma KS_ad_iwS_1_ok : BG.kept_ok 64 Pad_iwS.regs0 Pad_iwS.regs_out1 KS_ad_iwS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_075 ())). Qed.
Definition KS_ad_iwS_2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwS.regs0 Pad_iwS.regs_out2).
Lemma KS_ad_iwS_2_ok : BG.kept_ok 64 Pad_iwS.regs0 Pad_iwS.regs_out2 KS_ad_iwS_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_076 ())). Qed.
Definition KS_ad_iwS_3 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwS.regs0 Pad_iwS.regs_out3).
Lemma KS_ad_iwS_3_ok : BG.kept_ok 64 Pad_iwS.regs0 Pad_iwS.regs_out3 KS_ad_iwS_3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_077 ())). Qed.
Lemma ad_iwS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 35%nat) + ((V 34%nat) + 1)) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 35%nat) <= 140737488355304 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 35%nat) \/ (V 35%nat) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (V 35%nat) 24 -> L5.u8_at RSEGS M (V 35%nat) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> 0 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 ->
  0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3ce00 M')
        /\ (forall x, In x KS_ad_iwS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (V 35%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (2 * (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3ce2c M')
        /\ (forall x, In x KS_ad_iwS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ (V 37%nat) < (((V 35%nat) + 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3ce2c M')
        /\ (forall x, In x KS_ad_iwS_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ (((((V 34%nat) + (V 35%nat)) mod 2 ^ 64) + 2) mod 2 ^ 64) <= (V 37%nat)
        /\ (((V 35%nat) + 1) mod 2 ^ 64) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3cd58 M')
        /\ (forall x, In x KS_ad_iwS_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (V 35%nat)) + 2)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (V 37%nat) < (((((V 34%nat) + (V 35%nat)) mod 2 ^ 64) + 2) mod 2 ^ 64)
        /\ (((V 35%nat) + 1) mod 2 ^ 64) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_078 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_iwL := BndP_Ns_033.LibSegNs_ad_iwL.
Definition KS_ad_iwL_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwL.regs0 Pad_iwL.regs_out0).
Lemma KS_ad_iwL_0_ok : BG.kept_ok 64 Pad_iwL.regs0 Pad_iwL.regs_out0 KS_ad_iwL_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_079 ())). Qed.
Definition KS_ad_iwL_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwL.regs0 Pad_iwL.regs_out1).
Lemma KS_ad_iwL_1_ok : BG.kept_ok 64 Pad_iwL.regs0 Pad_iwL.regs_out1 KS_ad_iwL_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_080 ())). Qed.
Definition KS_ad_iwL_2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwL.regs0 Pad_iwL.regs_out2).
Lemma KS_ad_iwL_2_ok : BG.kept_ok 64 Pad_iwL.regs0 Pad_iwL.regs_out2 KS_ad_iwL_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_081 ())). Qed.
Definition KS_ad_iwL_3 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_iwL.regs0 Pad_iwL.regs_out3).
Lemma KS_ad_iwL_3_ok : BG.kept_ok 64 Pad_iwL.regs0 Pad_iwL.regs_out3 KS_ad_iwL_3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_082 ())). Qed.
Lemma ad_iwL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 39%nat) + (V 34%nat)) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 35%nat) <= 140737488355304 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 35%nat) \/ (V 35%nat) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (V 35%nat) 24 -> L5.u8_at RSEGS M (V 35%nat) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 536870912 ->
  L5.u64_at RSEGS M ((V 35%nat) + 16) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737487306752 -> 0 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 ->
  0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3ce00 M')
        /\ (forall x, In x KS_ad_iwL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 39%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3ce2c M')
        /\ (forall x, In x KS_ad_iwL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ (V 37%nat) < (V 39%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3ce2c M')
        /\ (forall x, In x KS_ad_iwL_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ (((((V 34%nat) + (V 39%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) <= (V 37%nat)
        /\ (V 39%nat) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ccec M) (st fx' R' 0x3cd58 M')
        /\ (forall x, In x KS_ad_iwL_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (V 39%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (V 37%nat) < (((((V 34%nat) + (V 39%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64)
        /\ (V 39%nat) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_083 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isS := BndP_Ns_033.LibSegNs_ad_isS.
Definition KS_ad_isS_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isS.regs0 Pad_isS.regs_out0).
Lemma KS_ad_isS_0_ok : BG.kept_ok 64 Pad_isS.regs0 Pad_isS.regs_out0 KS_ad_isS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_084 ())). Qed.
Definition KS_ad_isS_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isS.regs0 Pad_isS.regs_out1).
Lemma KS_ad_isS_1_ok : BG.kept_ok 64 Pad_isS.regs0 Pad_isS.regs_out1 KS_ad_isS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_085 ())). Qed.
Lemma ad_isS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 38%nat) -> Z.testbit (V 38%nat) 0 = false ->
  1 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3ce2c M) (st fx' R' 0x3cee8 M')
        /\ (forall x, In x KS_ad_isS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 22
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 34%nat)) + 22)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ (V 36%nat) <= ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ce2c M) (st fx' R' 0x662f8 M')
        /\ (forall x, In x KS_ad_isS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 249520
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 11) = Z_to_bv 64 22
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) + (V 36%nat)) - 22)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + 22) mod 2 ^ 64) < (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_086 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isL := BndP_Ns_033.LibSegNs_ad_isL.
Definition KS_ad_isL_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isL.regs0 Pad_isL.regs_out0).
Lemma KS_ad_isL_0_ok : BG.kept_ok 64 Pad_isL.regs0 Pad_isL.regs_out0 KS_ad_isL_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_087 ())). Qed.
Definition KS_ad_isL_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isL.regs0 Pad_isL.regs_out1).
Lemma KS_ad_isL_1_ok : BG.kept_ok 64 Pad_isL.regs0 Pad_isL.regs_out1 KS_ad_isL_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_088 ())). Qed.
Lemma ad_isL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 536870912 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737487306752 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 38%nat) -> 27 <= (V 38%nat) <= 1073741825 ->
  Z.testbit (V 38%nat) 0 = true -> 1 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3ce2c M) (st fx' R' 0x3cee8 M')
        /\ (forall x, In x KS_ad_isL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((2 * ((V 38%nat) / 2)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((-1) * (V 34%nat)) + (2 * ((V 38%nat) / 2))) - 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 (V 39%nat)
        /\ (V 36%nat) <= ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 38%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ce2c M) (st fx' R' 0x662f8 M')
        /\ (forall x, In x KS_ad_isL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 249520
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 11) = Z_to_bv 64 ((2 * ((V 38%nat) / 2)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) + ((V 36%nat) + ((-2) * ((V 38%nat) / 2)))) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 38%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) < (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_089 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isG := BndP_Ns_032.LibSegNs_ad_isG.
Definition KS_ad_isG : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isG.regs0 Pad_isG.regs_out0).
Lemma KS_ad_isG_ok : BG.kept_ok 64 Pad_isG.regs0 Pad_isG.regs_out0 KS_ad_isG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_090 ())). Qed.
Lemma ad_isG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 9))) + 16) (V 41%nat) ->
  0 <= (V 34%nat) <= 536870912 -> 1 <= (V 36%nat) <= 536870912 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 8) <= i < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ceb0 M) (st fx' R' 0x3cee8 M')
        /\ (forall x, In x KS_ad_isG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 (V 41%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 8) ((V 34%nat) + (V 36%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_091 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isTs := BndP_Ns_033.LibSegNs_ad_isTs.
Definition KS_ad_isTs : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isTs.regs0 Pad_isTs.regs_out0).
Lemma KS_ad_isTs_ok : BG.kept_ok 64 Pad_isTs.regs0 Pad_isTs.regs_out0 KS_ad_isTs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_092 ())). Qed.
Lemma ad_isTs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) -> getr R (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 9))) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> 1 <= (V 36%nat) <= 22 -> 1 <= ((V 34%nat) + (V 36%nat)) <= 22 ->
  0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 0) <= i < ((bv_unsigned (getr R (reg 9))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3cee8 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_isTs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 249632
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1) 0
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 9))) ((2 * (V 34%nat)) + (2 * (V 36%nat)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_093 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isTl := BndP_Ns_033.LibSegNs_ad_isTl.
Definition KS_ad_isTl : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isTl.regs0 Pad_isTl.regs_out0).
Lemma KS_ad_isTl_ok : BG.kept_ok 64 Pad_isTl.regs0 Pad_isTl.regs_out0 KS_ad_isTl = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_094 ())). Qed.
Lemma ad_isTl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) -> getr R (reg 21) = Z_to_bv 64 (V 41%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> 0 <= (V 34%nat) <= 536870912 -> 1 <= (V 36%nat) <= 536870912 ->
  4096 <= (V 41%nat) <= 140737487306752 -> L5.writable RSEGS M ((V 41%nat) + ((V 34%nat) + (V 36%nat))) 1 -> (((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 1 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 41%nat) + ((V 34%nat) + (V 36%nat)))) -> (((V 2%nat) - 64) + 64 <= ((V 41%nat) + ((V 34%nat) + (V 36%nat))) \/ ((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 1 <= ((V 2%nat) - 64)) ->
  0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> ~ ((((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) <= bv_unsigned a < (((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 8) <= i < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> ~ ((((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) <= i < (((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3cee8 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_isTl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 249632
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + ((V 36%nat) + (V 41%nat)))
        /\ L5.u8_at RSEGS M' ((V 34%nat) + ((V 36%nat) + (V 41%nat))) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 8) ((V 34%nat) + (V 36%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_095 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isRs := BndP_Ns_033.LibSegNs_ad_isRs.
Definition KS_ad_isRs : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isRs.regs0 Pad_isRs.regs_out0).
Lemma KS_ad_isRs_ok : BG.kept_ok 64 Pad_isRs.regs0 Pad_isRs.regs_out0 KS_ad_isRs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_096 ())). Qed.
Lemma ad_isRs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (2 * (V 42%nat)) ->
  0 <= (V 42%nat) <= 22 -> 0 <= (Z.land ((2 * (V 42%nat)) mod 2 ^ 64) 1) <= 0 -> 0 <= (V 34%nat) <= 22 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3cf20 M) (st fx' R' 0x3cf5c M')
        /\ (forall x, In x KS_ad_isRs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + (V 34%nat)) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_097 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_isRl := BndP_Ns_033.LibSegNs_ad_isRl.
Definition KS_ad_isRl : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isRl.regs0 Pad_isRl.regs_out0).
Lemma KS_ad_isRl_ok : BG.kept_ok 64 Pad_isRl.regs0 Pad_isRl.regs_out0 KS_ad_isRl = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_098 ())). Qed.
Lemma ad_isRl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 9))) + 16) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737487306752 ->
  0 <= (V 34%nat) <= 536870912 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3cf20 M) (st fx' R' 0x3cf5c M')
        /\ (forall x, In x KS_ad_isRl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsP ()) [] (Mh_0188_blobs1.kr_b_099 ())). Qed.
(* [comment removed for export] *)

End PQADINSP.

End PnAdSInsP.
Module PnAdSIns.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSInsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3c73c_3c740 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3c898_3c89c.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSIns () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS8src_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6mem_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib7Mh_00906L5Core3L5C9rdn_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS3BRXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c898_3c89c7W_3cf14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c898_3c89c7F_3cf14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c898_3c89c7D_3cf14C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5reg_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isRs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS7land2_0C1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6cs_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS;size_le_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isRsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isRl_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5sz_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isRlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6src_rdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS;src_out_hdrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2Bapart_of_pointwiseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2;memmove_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS;saves_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5ret_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5src_qC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS5ret_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isTs_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6move_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isTsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isTl_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6move_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isTlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_isG_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP9KS_ad_isGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6GB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6stk_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7gb_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS8saves_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS9mem_ok_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6back_GC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2>u64_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2<u64_low_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>testbit_even_0c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_isS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS4cndSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6tail_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS9grow_callC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_isS_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c73c_3c7407W_3cdb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c73c_3c7407F_3cdb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c73c_3c7407D_3cdb8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_iwS_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rc69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS8ret_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6safe_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS7mem_ok0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_iwL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS6safe_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS7entry_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS7entry_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6src_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSIns7PQADINS8ins_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ins_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADINS.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) [] (Mh_0188_blobs1.kr_b_100 ())). Qed.

Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) [] (Mh_0188_blobs1.kr_b_101 ())). Qed.

Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) [] (Mh_0188_blobs1.kr_b_102 ())). Qed.

(* [comment removed for export] *)
Lemma cndS sz : 0 <= sz <= 22 -> (((18446744073709551615 * sz) mod 2 ^ 64) + 22) mod 2 ^ 64 = 22 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) [] (Mh_0188_blobs1.kr_b_103 ())). Qed.
Lemma cndL sz w : 0 <= sz < 2 * (w / 2) -> 0 <= w < 2 ^ 62 ->
  (((((18446744073709551615 * sz) mod 2 ^ 64) + ((2 * (w / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = 2 * (w / 2) - 1 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) [] (Mh_0188_blobs1.kr_b_104 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_at_agree (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> L5C.agree_on M M' o 24 -> (forall c n p, x = PM.VLong c n p -> L5.defined M' p c) ->
  kstr_at M o x -> kstr_at M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) [] (Mh_0188_blobs1.kr_b_105 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.
Let GB := PQADGB.gb_ok L HI LY HIok OPN OPD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o q n S r SM g : Z) (x : PM.vstr).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 q.
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 (q + n).
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n.
Hypothesis Hroom : PM.vs_size x + n <= SM.
Hypothesis SRC : PQAS.src_ok RSEGS L M0 LB S o q n.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
  L5C.hpres L LB S 14336 [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let sz : Z := PM.vs_size x.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_106 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_107 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14336 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14336 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_108 ())). Qed.

Lemma cap_ge : 22 <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_109 ())). Qed.
Lemma size_le_cap : 0 <= sz <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_110 ())). Qed.
Lemma sz_SM : 0 <= sz <= SM /\ SM <= 2 ^ 29.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_111 ())). Qed.

(* [comment removed for export] *)
Lemma src_q : 0 <= q /\ q + n < 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_112 ())). Qed.
Lemma src_kept i : 0 <= i < n -> L5C.kept L LB S 14336 [(o, 24)] (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_113 ())). Qed.
Lemma src_out_hdr i : 0 <= i < n -> ~ (o <= q + i < o + 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_114 ())). Qed.
Lemma src_client i : 0 <= i < n -> client_addr L LB S 14336 (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_115 ())). Qed.
(* [comment removed for export] *)
Lemma src_rd M : mem_ok M -> exists bs, length bs = Z.to_nat n /\ rdn RSEGS M (Z_to_bv 64 q) (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_116 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_117 ())). Qed.

Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 64 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_118 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (x' : PM.vstr) (g' : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  kstr_at M1 o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = sz + n -> mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') -> model_but_vm model0 model1 ->
  hi_heap HI (PM.vs_own x' ++ LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cf5c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_119 ())). Qed.

(* [comment removed for export] *)
Lemma cs_fin (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S ->
  getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R0 (reg k)) ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_120 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VShort (sz + n)) -> sz + n <= 22 ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cf20 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_121 ())). Qed.

(* [comment removed for export] *)
Lemma ret_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cf20 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_122 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma move_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 1) = Z_to_bv 64 0x3cf20 -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (o + 1 + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> L5.u8_at RSEGS M1 o (2 * (sz + n)) ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_123 ())). Qed.

(* [comment removed for export] *)
Lemma move_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 1) = Z_to_bv 64 0x3cf20 -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (d + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_124 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 (o + 1) ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cee8 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_125 ())). Qed.

(* [comment removed for export] *)
Lemma tail_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 d ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (c' + 1) -> L5.u64_at RSEGS M1 (o + 16) d -> L5.defined M1 d c' -> sz + n < c' -> 26 <= c' <= PQM.KCAP -> c' mod 2 = 0 ->
  PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' -> (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cee8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_126 ())). Qed.

(* [comment removed for export] *)
Lemma back_G (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (A + 1) -> L5.u64_at RSEGS M1 (o + 16) B -> L5.defined M1 B A -> sz + n < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
  PQM.ks_ok SM (PM.VLong A (sz + n) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (sz + n) B) (g + 1)) -> model_but_vm model0 model1 ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ceb0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_127 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_gb M2 M3 : saves M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_128 ())). Qed.
Lemma mem_ok_gb M2 M3 : mem_ok M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5.defined M3 o 24 -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_129 ())). Qed.
Lemma stk_gb M2 : mem_ok M2 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_130 ())). Qed.

(* [comment removed for export] *)
Lemma grow_call (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) :
  1 <= n -> PM.vs_cap x < sz + n ->
  getr R2 (reg 1) = Z_to_bv 64 0x3ceb0 -> getr R2 (reg 2) = Z_to_bv 64 (S - 64) -> getr R2 (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (reg 8) = Z_to_bv 64 sz -> getr R2 (reg 9) = Z_to_bv 64 o -> getr R2 (reg 10) = Z_to_bv 64 o -> getr R2 (reg 11) = Z_to_bv 64 (PM.vs_cap x) ->
  getr R2 (reg 12) = Z_to_bv 64 (sz + n - PM.vs_cap x) -> getr R2 (reg 13) = Z_to_bv 64 sz -> getr R2 (reg 14) = Z_to_bv 64 sz -> getr R2 (reg 15) = Z_to_bv 64 0 ->
  getr R2 (reg 18) = Z_to_bv 64 q -> getr R2 (reg 19) = Z_to_bv 64 (q + n) -> getr R2 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R2 -> saves M2 -> mem_ok M2 -> kstr_at M2 o x -> hi_heap HI (PM.vs_own x ++ LB) cr0 M2 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x662f8 M2 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_131 ())). Qed.

(* [comment removed for export] *)
Lemma safe_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ce2c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_132 ())). Qed.

(* [comment removed for export] *)
Lemma safe_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c sz0 p : Z) :
  x = PM.VLong c sz0 p -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> hi_heap HI ((p, c) :: LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ce2c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_133 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_zero (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  n = 0 -> (forall k, In k (1%nat :: PMK.cs_all) -> getr R1 (reg k) = getr R0 (reg k)) -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ce00 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_134 ())). Qed.

(* [comment removed for export] *)
Lemma entry_S (sz0 : Z) : x = PM.VShort sz0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3ccec M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_135 ())). Qed.

(* [comment removed for export] *)
Lemma entry_L (c sz0 p : Z) : x = PM.VLong c sz0 p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3ccec M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_136 ())). Qed.

(* [comment removed for export] *)
Lemma ins_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3ccec M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_137 ())). Qed.

End Call.

Theorem ins_ok : PQAS.ins_spec RSEGS AD L HI 0x3ccec.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSIns ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_138 ())). Qed.




End WithHeap.
End PQADINS.

End PnAdSIns.
Module PnAdSJnsP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSJnsP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS9regs_out3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_3C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwS_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwS_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwS_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS6cells3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwS3ps3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwS_3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL9regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL9regs_out3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwL_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL6cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwL_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL6cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwL_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL6cells3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jwL3ps3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jwL_3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsS_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsS_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS6cells0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsS3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jsS_0_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jsS_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsL_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsL_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za07C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsL3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jsL_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP>KS_ad_jsL_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP9KS_ad_jsGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<KS_ad_jsG_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7Pad_jsG6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsTsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP=KS_ad_jsTs_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTs6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsTlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP=KS_ad_jsTl_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsTl6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsRsC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRs3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP=KS_ad_jsRs_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsRlC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP8Pad_jsRl3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP=KS_ad_jsRl_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADJNSP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_139 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_140 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_141 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_142 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_143 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_144 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_145 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_146 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_147 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_148 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_149 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_150 ())). Qed.
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
Module Pad_jwS := BndP_Ns_034.LibSegNs_ad_jwS.
Definition KS_ad_jwS_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwS.regs0 Pad_jwS.regs_out0).
Lemma KS_ad_jwS_0_ok : BG.kept_ok 64 Pad_jwS.regs0 Pad_jwS.regs_out0 KS_ad_jwS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_151 ())). Qed.
Definition KS_ad_jwS_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwS.regs0 Pad_jwS.regs_out1).
Lemma KS_ad_jwS_1_ok : BG.kept_ok 64 Pad_jwS.regs0 Pad_jwS.regs_out1 KS_ad_jwS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_152 ())). Qed.
Definition KS_ad_jwS_2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwS.regs0 Pad_jwS.regs_out2).
Lemma KS_ad_jwS_2_ok : BG.kept_ok 64 Pad_jwS.regs0 Pad_jwS.regs_out2 KS_ad_jwS_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_153 ())). Qed.
Definition KS_ad_jwS_3 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwS.regs0 Pad_jwS.regs_out3).
Lemma KS_ad_jwS_3_ok : BG.kept_ok 64 Pad_jwS.regs0 Pad_jwS.regs_out3 KS_ad_jwS_3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_154 ())). Qed.
Lemma ad_jwS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 35%nat) + ((V 34%nat) + 1)) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 35%nat) <= 140737488355304 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 35%nat) \/ (V 35%nat) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (V 35%nat) 24 -> L5.u8_at RSEGS M (V 35%nat) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> 0 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 ->
  0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea1c M')
        /\ (forall x, In x KS_ad_jwS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (V 35%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (2 * (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea48 M')
        /\ (forall x, In x KS_ad_jwS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ (V 37%nat) < (((V 35%nat) + 1) mod 2 ^ 64)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea48 M')
        /\ (forall x, In x KS_ad_jwS_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ (((((V 34%nat) + (V 35%nat)) mod 2 ^ 64) + 2) mod 2 ^ 64) <= (V 37%nat)
        /\ (((V 35%nat) + 1) mod 2 ^ 64) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3e974 M')
        /\ (forall x, In x KS_ad_jwS_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (V 35%nat)) + 2)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (V 37%nat) < (((((V 34%nat) + (V 35%nat)) mod 2 ^ 64) + 2) mod 2 ^ 64)
        /\ (((V 35%nat) + 1) mod 2 ^ 64) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_155 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jwL := BndP_Ns_034.LibSegNs_ad_jwL.
Definition KS_ad_jwL_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwL.regs0 Pad_jwL.regs_out0).
Lemma KS_ad_jwL_0_ok : BG.kept_ok 64 Pad_jwL.regs0 Pad_jwL.regs_out0 KS_ad_jwL_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_156 ())). Qed.
Definition KS_ad_jwL_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwL.regs0 Pad_jwL.regs_out1).
Lemma KS_ad_jwL_1_ok : BG.kept_ok 64 Pad_jwL.regs0 Pad_jwL.regs_out1 KS_ad_jwL_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_157 ())). Qed.
Definition KS_ad_jwL_2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwL.regs0 Pad_jwL.regs_out2).
Lemma KS_ad_jwL_2_ok : BG.kept_ok 64 Pad_jwL.regs0 Pad_jwL.regs_out2 KS_ad_jwL_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_158 ())). Qed.
Definition KS_ad_jwL_3 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jwL.regs0 Pad_jwL.regs_out3).
Lemma KS_ad_jwL_3_ok : BG.kept_ok 64 Pad_jwL.regs0 Pad_jwL.regs_out3 KS_ad_jwL_3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_159 ())). Qed.
Lemma ad_jwL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 39%nat) + (V 34%nat)) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 35%nat) <= 140737488355304 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 35%nat) \/ (V 35%nat) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (V 35%nat) 24 -> L5.u8_at RSEGS M (V 35%nat) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 536870912 ->
  L5.u64_at RSEGS M ((V 35%nat) + 16) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737487306752 -> 0 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 ->
  0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea1c M')
        /\ (forall x, In x KS_ad_jwL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 39%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea48 M')
        /\ (forall x, In x KS_ad_jwL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ (V 37%nat) < (V 39%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea48 M')
        /\ (forall x, In x KS_ad_jwL_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ (((((V 34%nat) + (V 39%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) <= (V 37%nat)
        /\ (V 39%nat) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3e974 M')
        /\ (forall x, In x KS_ad_jwL_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (V 39%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (V 37%nat) < (((((V 34%nat) + (V 39%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64)
        /\ (V 39%nat) <= (V 37%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_160 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsS := BndP_Ns_033.LibSegNs_ad_jsS.
Definition KS_ad_jsS_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsS.regs0 Pad_jsS.regs_out0).
Lemma KS_ad_jsS_0_ok : BG.kept_ok 64 Pad_jsS.regs0 Pad_jsS.regs_out0 KS_ad_jsS_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_161 ())). Qed.
Definition KS_ad_jsS_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsS.regs0 Pad_jsS.regs_out1).
Lemma KS_ad_jsS_1_ok : BG.kept_ok 64 Pad_jsS.regs0 Pad_jsS.regs_out1 KS_ad_jsS_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_162 ())). Qed.
Lemma ad_jsS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 38%nat) -> Z.testbit (V 38%nat) 0 = false ->
  1 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3ea48 M) (st fx' R' 0x3eb04 M')
        /\ (forall x, In x KS_ad_jsS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 22
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 34%nat)) + 22)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 1)
        /\ (V 36%nat) <= ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + 22) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ea48 M) (st fx' R' 0x662f8 M')
        /\ (forall x, In x KS_ad_jsS_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 256716
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 11) = Z_to_bv 64 22
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) + (V 36%nat)) - 22)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + 22) mod 2 ^ 64) < (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_163 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsL := BndP_Ns_033.LibSegNs_ad_jsL.
Definition KS_ad_jsL_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsL.regs0 Pad_jsL.regs_out0).
Lemma KS_ad_jsL_0_ok : BG.kept_ok 64 Pad_jsL.regs0 Pad_jsL.regs_out0 KS_ad_jsL_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_164 ())). Qed.
Definition KS_ad_jsL_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsL.regs0 Pad_jsL.regs_out1).
Lemma KS_ad_jsL_1_ok : BG.kept_ok 64 Pad_jsL.regs0 Pad_jsL.regs_out1 KS_ad_jsL_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_165 ())). Qed.
Lemma ad_jsL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 536870912 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737487306752 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 38%nat) -> 27 <= (V 38%nat) <= 1073741825 ->
  Z.testbit (V 38%nat) 0 = true -> 1 <= (V 36%nat) <= 536870912 -> 0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3ea48 M) (st fx' R' 0x3eb04 M')
        /\ (forall x, In x KS_ad_jsL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((2 * ((V 38%nat) / 2)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((((-1) * (V 34%nat)) + (2 * ((V 38%nat) / 2))) - 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 (V 39%nat)
        /\ (V 36%nat) <= ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 38%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3ea48 M) (st fx' R' 0x662f8 M')
        /\ (forall x, In x KS_ad_jsL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 256716
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 11) = Z_to_bv 64 ((2 * ((V 38%nat) / 2)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) + ((V 36%nat) + ((-2) * ((V 38%nat) / 2)))) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat))
        /\ ((((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + ((2 * ((V 38%nat) / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) < (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_166 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsG := BndP_Ns_033.LibSegNs_ad_jsG.
Definition KS_ad_jsG : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsG.regs0 Pad_jsG.regs_out0).
Lemma KS_ad_jsG_ok : BG.kept_ok 64 Pad_jsG.regs0 Pad_jsG.regs_out0 KS_ad_jsG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_167 ())). Qed.
Lemma ad_jsG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 9))) + 16) (V 41%nat) ->
  0 <= (V 34%nat) <= 536870912 -> 1 <= (V 36%nat) <= 536870912 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 8) <= i < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3eacc M) (st fx' R' 0x3eb04 M')
        /\ (forall x, In x KS_ad_jsG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 (V 41%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 8) ((V 34%nat) + (V 36%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_168 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsTs := BndP_Ns_034.LibSegNs_ad_jsTs.
Definition KS_ad_jsTs : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsTs.regs0 Pad_jsTs.regs_out0).
Lemma KS_ad_jsTs_ok : BG.kept_ok 64 Pad_jsTs.regs0 Pad_jsTs.regs_out0 KS_ad_jsTs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_169 ())). Qed.
Lemma ad_jsTs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) -> getr R (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 9))) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> 1 <= (V 36%nat) <= 22 -> 1 <= ((V 34%nat) + (V 36%nat)) <= 22 ->
  0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 0) <= i < ((bv_unsigned (getr R (reg 9))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3eb04 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_jsTs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 256828
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1) 0
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 9))) ((2 * (V 34%nat)) + (2 * (V 36%nat)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_170 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsTl := BndP_Ns_034.LibSegNs_ad_jsTl.
Definition KS_ad_jsTl : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsTl.regs0 Pad_jsTl.regs_out0).
Lemma KS_ad_jsTl_ok : BG.kept_ok 64 Pad_jsTl.regs0 Pad_jsTl.regs_out0 KS_ad_jsTl = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_171 ())). Qed.
Lemma ad_jsTl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) -> getr R (reg 21) = Z_to_bv 64 (V 41%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> 0 <= (V 34%nat) <= 536870912 -> 1 <= (V 36%nat) <= 536870912 ->
  4096 <= (V 41%nat) <= 140737487306752 -> L5.writable RSEGS M ((V 41%nat) + ((V 34%nat) + (V 36%nat))) 1 -> (((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 1 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 41%nat) + ((V 34%nat) + (V 36%nat)))) -> (((V 2%nat) - 64) + 64 <= ((V 41%nat) + ((V 34%nat) + (V 36%nat))) \/ ((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 1 <= ((V 2%nat) - 64)) ->
  0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> ~ ((((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) <= bv_unsigned a < (((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 8) <= i < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> ~ ((((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) <= i < (((V 41%nat) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3eb04 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_jsTl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 256828
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 34%nat) + ((V 36%nat) + (V 41%nat)))
        /\ L5.u8_at RSEGS M' ((V 34%nat) + ((V 36%nat) + (V 41%nat))) 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 8) ((V 34%nat) + (V 36%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_172 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsRs := BndP_Ns_033.LibSegNs_ad_jsRs.
Definition KS_ad_jsRs : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsRs.regs0 Pad_jsRs.regs_out0).
Lemma KS_ad_jsRs_ok : BG.kept_ok 64 Pad_jsRs.regs0 Pad_jsRs.regs_out0 KS_ad_jsRs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_173 ())). Qed.
Lemma ad_jsRs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (2 * (V 42%nat)) ->
  0 <= (V 42%nat) <= 22 -> 0 <= (Z.land ((2 * (V 42%nat)) mod 2 ^ 64) 1) <= 0 -> 0 <= (V 34%nat) <= 22 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3eb3c M) (st fx' R' 0x3eb78 M')
        /\ (forall x, In x KS_ad_jsRs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + (V 34%nat)) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_174 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_jsRl := BndP_Ns_033.LibSegNs_ad_jsRl.
Definition KS_ad_jsRl : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsRl.regs0 Pad_jsRl.regs_out0).
Lemma KS_ad_jsRl_ok : BG.kept_ok 64 Pad_jsRl.regs0 Pad_jsRl.regs_out0 KS_ad_jsRl = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_175 ())). Qed.
Lemma ad_jsRl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (V 33%nat) ->
  0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 9))) + 16) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737487306752 ->
  0 <= (V 34%nat) <= 536870912 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3eb3c M) (st fx' R' 0x3eb78 M')
        /\ (forall x, In x KS_ad_jsRl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 41%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsP ()) [] (Mh_0188_blobs1.kr_b_176 ())). Qed.
(* [comment removed for export] *)

End PQADJNSP.

End PnAdSJnsP.
Module PnAdSJns.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJnsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3e358_3e35c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3e4b4_3e4b8.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSJns () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS8src_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6mem_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC69OSSVerify5KrLib7Mh_00906L5Core3L5C9rdn_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS3BRXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e4b4_3e4b87W_3eb30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e4b4_3e4b87F_3eb30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e4b4_3e4b87D_3eb30C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indc69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5reg_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsRs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS7land2_0C1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6cs_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS;size_le_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsRsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsRl_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5sz_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsRlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6src_rdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS;src_out_hdrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2Bapart_of_pointwiseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2;memmove_rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS;saves_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5ret_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5src_qC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subc69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS5ret_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsTs_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6move_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsTsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsTl_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6move_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsTlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jsG_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP9KS_ad_jsGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6GB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6stk_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB7gb_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS8saves_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS9mem_ok_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6back_GC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2>u64_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2<u64_low_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>testbit_even_0c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jsS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS4cndSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6tail_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS9grow_callC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jsS_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7W_3e9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7F_3e9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7D_3e9d4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jwS_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rc69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS8ret_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6safe_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS7mem_ok0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jwL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS6safe_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwL_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS7entry_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS7entry_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6src_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSJns7PQADJNS8ins_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ins_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADJNS.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) [] (Mh_0188_blobs1.kr_b_177 ())). Qed.

Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) [] (Mh_0188_blobs1.kr_b_178 ())). Qed.

Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) [] (Mh_0188_blobs1.kr_b_179 ())). Qed.

(* [comment removed for export] *)
Lemma cndS sz : 0 <= sz <= 22 -> (((18446744073709551615 * sz) mod 2 ^ 64) + 22) mod 2 ^ 64 = 22 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) [] (Mh_0188_blobs1.kr_b_180 ())). Qed.
Lemma cndL sz w : 0 <= sz < 2 * (w / 2) -> 0 <= w < 2 ^ 62 ->
  (((((18446744073709551615 * sz) mod 2 ^ 64) + ((2 * (w / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = 2 * (w / 2) - 1 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) [] (Mh_0188_blobs1.kr_b_181 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_at_agree (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> L5C.agree_on M M' o 24 -> (forall c n p, x = PM.VLong c n p -> L5.defined M' p c) ->
  kstr_at M o x -> kstr_at M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) [] (Mh_0188_blobs1.kr_b_182 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.
Let GB := PQADGB.gb_ok L HI LY HIok OPN OPD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o q n S r SM g : Z) (x : PM.vstr).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 q.
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 (q + n).
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n.
Hypothesis Hroom : PM.vs_size x + n <= SM.
Hypothesis SRC : PQAS.src_ok RSEGS L M0 LB S o q n.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
  L5C.hpres L LB S 14336 [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let sz : Z := PM.vs_size x.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_183 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_184 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14336 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14336 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_185 ())). Qed.

Lemma cap_ge : 22 <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_186 ())). Qed.
Lemma size_le_cap : 0 <= sz <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_187 ())). Qed.
Lemma sz_SM : 0 <= sz <= SM /\ SM <= 2 ^ 29.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_188 ())). Qed.

(* [comment removed for export] *)
Lemma src_q : 0 <= q /\ q + n < 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_189 ())). Qed.
Lemma src_kept i : 0 <= i < n -> L5C.kept L LB S 14336 [(o, 24)] (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_190 ())). Qed.
Lemma src_out_hdr i : 0 <= i < n -> ~ (o <= q + i < o + 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_191 ())). Qed.
Lemma src_client i : 0 <= i < n -> client_addr L LB S 14336 (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_192 ())). Qed.
(* [comment removed for export] *)
Lemma src_rd M : mem_ok M -> exists bs, length bs = Z.to_nat n /\ rdn RSEGS M (Z_to_bv 64 q) (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_193 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_194 ())). Qed.

Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 64 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_195 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (x' : PM.vstr) (g' : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  kstr_at M1 o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = sz + n -> mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') -> model_but_vm model0 model1 ->
  hi_heap HI (PM.vs_own x' ++ LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb78 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_196 ())). Qed.

(* [comment removed for export] *)
Lemma cs_fin (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S ->
  getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R0 (reg k)) ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_197 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VShort (sz + n)) -> sz + n <= 22 ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb3c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_198 ())). Qed.

(* [comment removed for export] *)
Lemma ret_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb3c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_199 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma move_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 1) = Z_to_bv 64 0x3eb3c -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (o + 1 + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> L5.u8_at RSEGS M1 o (2 * (sz + n)) ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_200 ())). Qed.

(* [comment removed for export] *)
Lemma move_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 1) = Z_to_bv 64 0x3eb3c -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (d + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_201 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 (o + 1) ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb04 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_202 ())). Qed.

(* [comment removed for export] *)
Lemma tail_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 d ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (c' + 1) -> L5.u64_at RSEGS M1 (o + 16) d -> L5.defined M1 d c' -> sz + n < c' -> 26 <= c' <= PQM.KCAP -> c' mod 2 = 0 ->
  PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' -> (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb04 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_203 ())). Qed.

(* [comment removed for export] *)
Lemma back_G (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (A + 1) -> L5.u64_at RSEGS M1 (o + 16) B -> L5.defined M1 B A -> sz + n < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
  PQM.ks_ok SM (PM.VLong A (sz + n) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (sz + n) B) (g + 1)) -> model_but_vm model0 model1 ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eacc M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_204 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_gb M2 M3 : saves M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_205 ())). Qed.
Lemma mem_ok_gb M2 M3 : mem_ok M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5.defined M3 o 24 -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_206 ())). Qed.
Lemma stk_gb M2 : mem_ok M2 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_207 ())). Qed.

(* [comment removed for export] *)
Lemma grow_call (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) :
  1 <= n -> PM.vs_cap x < sz + n ->
  getr R2 (reg 1) = Z_to_bv 64 0x3eacc -> getr R2 (reg 2) = Z_to_bv 64 (S - 64) -> getr R2 (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (reg 8) = Z_to_bv 64 sz -> getr R2 (reg 9) = Z_to_bv 64 o -> getr R2 (reg 10) = Z_to_bv 64 o -> getr R2 (reg 11) = Z_to_bv 64 (PM.vs_cap x) ->
  getr R2 (reg 12) = Z_to_bv 64 (sz + n - PM.vs_cap x) -> getr R2 (reg 13) = Z_to_bv 64 sz -> getr R2 (reg 14) = Z_to_bv 64 sz -> getr R2 (reg 15) = Z_to_bv 64 0 ->
  getr R2 (reg 18) = Z_to_bv 64 q -> getr R2 (reg 19) = Z_to_bv 64 (q + n) -> getr R2 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R2 -> saves M2 -> mem_ok M2 -> kstr_at M2 o x -> hi_heap HI (PM.vs_own x ++ LB) cr0 M2 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x662f8 M2 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_208 ())). Qed.

(* [comment removed for export] *)
Lemma safe_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ea48 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_209 ())). Qed.

(* [comment removed for export] *)
Lemma safe_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c sz0 p : Z) :
  x = PM.VLong c sz0 p -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> hi_heap HI ((p, c) :: LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ea48 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_210 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_zero (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  n = 0 -> (forall k, In k (1%nat :: PMK.cs_all) -> getr R1 (reg k) = getr R0 (reg k)) -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ea1c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_211 ())). Qed.

(* [comment removed for export] *)
Lemma entry_S (sz0 : Z) : x = PM.VShort sz0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3e908 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_212 ())). Qed.

(* [comment removed for export] *)
Lemma entry_L (c sz0 p : Z) : x = PM.VLong c sz0 p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3e908 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_213 ())). Qed.

(* [comment removed for export] *)
Lemma ins_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3e908 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_214 ())). Qed.

End Call.

Theorem ins_ok : PQAS.ins_spec RSEGS AD L HI 0x3e908.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJns ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_215 ())). Qed.




End WithHeap.
End PQADJNS.

End PnAdSJns.
Module PnAdSPbP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSPbP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbS_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbSGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbSG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP=KS_ad_pbSG_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbL0_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL09regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbL0_1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL0<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL03ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL03ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbL03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP?KS_ad_pbL0_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP?KS_ad_pbL0_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbLIC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLI3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP=KS_ad_pbLI_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbLGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP8Pad_pbLG3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP=KS_ad_pbLG_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbMC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbM3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbM_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbTC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbT3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbT_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbDC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbD3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbD_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF<seg_sound_axC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7Pad_pbF3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbF_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADPBP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_216 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_217 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_218 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_219 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_220 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_221 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_222 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_223 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_224 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_225 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_226 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_227 ())). Qed.
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
Module Pad_pbS := BndP_Ns_036.LibSegNs_ad_pbS.
Definition KS_ad_pbS : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbS.regs0 Pad_pbS.regs_out0).
Lemma KS_ad_pbS_ok : BG.kept_ok 64 Pad_pbS.regs0 Pad_pbS.regs_out0 KS_ad_pbS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_228 ())). Qed.
Lemma ad_pbS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (2 * (V 34%nat)) -> 0 <= (V 34%nat) <= 21 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66444 M) (st fx' R' 0x66574 M')
        /\ (forall x, In x KS_ad_pbS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((2 * (V 34%nat)) + 2)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 2) 0
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1) (bv_unsigned (getr R (reg 11)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) ((2 * (V 34%nat)) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_229 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbSG := BndP_Ns_036.LibSegNs_ad_pbSG.
Definition KS_ad_pbSG : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbSG.regs0 Pad_pbSG.regs_out0).
Lemma KS_ad_pbSG_ok : BG.kept_ok 64 Pad_pbSG.regs0 Pad_pbSG.regs_out0 KS_ad_pbSG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_230 ())). Qed.
Lemma ad_pbSG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) 44 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66444 M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_ad_pbSG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 419080
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
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_231 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbL0 := BndP_Ns_036.LibSegNs_ad_pbL0.
Definition KS_ad_pbL0_0 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbL0.regs0 Pad_pbL0.regs_out0).
Lemma KS_ad_pbL0_0_ok : BG.kept_ok 64 Pad_pbL0.regs0 Pad_pbL0.regs_out0 KS_ad_pbL0_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_232 ())). Qed.
Definition KS_ad_pbL0_1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbL0.regs0 Pad_pbL0.regs_out1).
Lemma KS_ad_pbL0_1_ok : BG.kept_ok 64 Pad_pbL0.regs0 Pad_pbL0.regs_out1 KS_ad_pbL0_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_233 ())). Qed.
Lemma ad_pbL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> 0 <= (V 33%nat) <= 255 -> Z.testbit (V 33%nat) 0 = true -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) ((2 * (V 35%nat)) + 1) ->
  13 <= (V 35%nat) <= 1073741824 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 2147483648 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x66444 M) (st fx' R' 0x66538 M')
        /\ (forall x, In x KS_ad_pbL0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 ((2 * (V 35%nat)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (2 * (V 35%nat))
        /\ 1 <= (((V 34%nat) - ((((2 * (V 35%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x66444 M) (st fx' R' 0x664ac M')
        /\ (forall x, In x KS_ad_pbL0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 11)
        /\ getr R' (reg 9) = getr R (reg 10)
        /\ getr R' (reg 10) = Z_to_bv 64 ((2 * (V 35%nat)) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (2 * (V 35%nat))
        /\ (((V 34%nat) - ((((2 * (V 35%nat)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_234 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbLI := BndP_Ns_036.LibSegNs_ad_pbLI.
Definition KS_ad_pbLI : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbLI.regs0 Pad_pbLI.regs_out0).
Lemma KS_ad_pbLI_ok : BG.kept_ok 64 Pad_pbLI.regs0 Pad_pbLI.regs_out0 KS_ad_pbLI = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_235 ())). Qed.
Lemma ad_pbLI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> 0 <= (bv_unsigned (getr R (reg 8))) <= 255 ->
  0 <= (bv_unsigned (getr R (reg 20))) <= 2147483648 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 9))) + 16) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737487306752 -> L5.writable RSEGS M ((bv_unsigned (getr R (reg 20))) + (V 37%nat)) 2 ->
  (((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 2 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((bv_unsigned (getr R (reg 20))) + (V 37%nat))) -> (((V 2%nat) - 64) + 64 <= ((bv_unsigned (getr R (reg 20))) + (V 37%nat)) \/ ((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 2 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 9))) + 8) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> ~ ((((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 0) <= bv_unsigned a < (((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 9))) + 8) <= i < ((bv_unsigned (getr R (reg 9))) + 8) + 8) -> ~ ((((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 0) <= i < (((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66538 M) (st fx' R' 0x66574 M')
        /\ (forall x, In x KS_ad_pbLI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((bv_unsigned (getr R (reg 20))) + (V 37%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((bv_unsigned (getr R (reg 20))) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 20))) + (V 37%nat)) + 1) 0
        /\ L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 20))) + (V 37%nat)) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 8) ((bv_unsigned (getr R (reg 20))) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_236 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbLG := BndP_Ns_036.LibSegNs_ad_pbLG.
Definition KS_ad_pbLG : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbLG.regs0 Pad_pbLG.regs_out0).
Lemma KS_ad_pbLG_ok : BG.kept_ok 64 Pad_pbLG.regs0 Pad_pbLG.regs_out0 KS_ad_pbLG = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_237 ())). Qed.
Lemma ad_pbLG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 10) = Z_to_bv 64 ((2 * (V 35%nat)) - 1) -> getr R (reg 20) = Z_to_bv 64 ((2 * (V 35%nat)) - 1) -> getr R (reg 21) = Z_to_bv 64 (2 * (V 35%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> 13 <= (V 35%nat) <= 1073741824 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 9))) + 16) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x664ac M) (st fx' R' 0xbe8b0 M')
        /\ (forall x, In x KS_ad_pbLG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 419080
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * (((4 * (V 35%nat)) - 2) / 8)) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 12
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((8 * (((4 * (V 35%nat)) - 2) / 8)) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_238 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbM := BndP_Ns_036.LibSegNs_ad_pbM.
Definition KS_ad_pbM : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbM.regs0 Pad_pbM.regs_out0).
Lemma KS_ad_pbM_ok : BG.kept_ok 64 Pad_pbM.regs0 Pad_pbM.regs_out0 KS_ad_pbM = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_239 ())). Qed.
Lemma ad_pbM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66508 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_pbM -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 419096
        /\ getr R' (reg 11) = getr R (reg 18)
        /\ getr R' (reg 12) = getr R (reg 20)
        /\ getr R' (reg 22) = getr R (reg 10)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_240 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbT := BndP_Ns_036.LibSegNs_ad_pbT.
Definition KS_ad_pbT : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbT.regs0 Pad_pbT.regs_out0).
Lemma KS_ad_pbT_ok : BG.kept_ok 64 Pad_pbT.regs0 Pad_pbT.regs_out0 KS_ad_pbT = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_241 ())). Qed.
Lemma ad_pbT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 23 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66518 M) (st fx' R' 0x6652c M')
        /\ (forall x, In x KS_ad_pbT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 23).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_242 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbD := BndP_Ns_036.LibSegNs_ad_pbD.
Definition KS_ad_pbD : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbD.regs0 Pad_pbD.regs_out0).
Lemma KS_ad_pbD_ok : BG.kept_ok 64 Pad_pbD.regs0 Pad_pbD.regs_out0 KS_ad_pbD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_243 ())). Qed.
Lemma ad_pbD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 21) = Z_to_bv 64 (2 * (V 35%nat)) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 13 <= (V 35%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66518 M) (st fx' R' 0x63dc4 M')
        /\ (forall x, In x KS_ad_pbD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 419116
        /\ getr R' (reg 10) = getr R (reg 18)
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 35%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_244 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_pbF := BndP_Ns_036.LibSegNs_ad_pbF.
Definition KS_ad_pbF : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbF.regs0 Pad_pbF.regs_out0).
Lemma KS_ad_pbF_ok : BG.kept_ok 64 Pad_pbF.regs0 Pad_pbF.regs_out0 KS_ad_pbF = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_245 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ad_pbF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> 0 <= (bv_unsigned (getr R (reg 8))) <= 255 ->
  0 <= (bv_unsigned (getr R (reg 20))) <= 2147483648 -> 48 <= (bv_unsigned (getr R (reg 19))) <= 2147483648 -> 4096 <= (bv_unsigned (getr R (reg 22))) <= 140737487306752 -> L5.writable RSEGS M ((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) 2 ->
  (((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 2 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22))))) -> (((V 2%nat) - 64) + 64 <= ((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) \/ ((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 2 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 47%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 24) -> ~ ((((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 0) <= bv_unsigned a < (((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 9))) + 0) <= i < ((bv_unsigned (getr R (reg 9))) + 0) + 24) -> ~ ((((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 0) <= i < (((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x6652c M) (st fx' R' 0x66574 M')
        /\ (forall x, In x KS_ad_pbF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22))))
        /\ getr R' (reg 11) = Z_to_bv 64 ((bv_unsigned (getr R (reg 20))) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) + 1) 0
        /\ L5.u8_at RSEGS M' ((bv_unsigned (getr R (reg 20))) + (bv_unsigned (getr R (reg 22)))) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 8) ((bv_unsigned (getr R (reg 20))) + 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 9))) + 16) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 9))) ((2 * ((bv_unsigned (getr R (reg 19))) / 2)) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 41%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbP ()) [] (Mh_0188_blobs1.kr_b_246 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

End PQADPBP.

End PnAdSPbP.
Module PnAdSPb.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPbP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r62890_62894.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSPb () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr06C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB3BRXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62890_628947W_6652cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62890_628947F_6652cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62890_628947D_6652cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6sub_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega:ZMicromega;ZArithProof01K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB7land2_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB<mem_ok_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB7cs_backC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB7mem_ok0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbLI_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbLIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB5reg_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbF_concC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbT_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6tail_FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbTC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbD_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opdel_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR7inW_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR<defined_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbM_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove5PMCPS;memmove_runC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB;saves_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6tail_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6tail_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPNEW_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbSG_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ks_growC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS;pot_ks_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB7stk_newC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS<opnew_spec_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;fresh_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBfresh_block_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB<saves_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB=mem_ok_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB;after_new_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbSGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS4NREQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbLG_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9gcount_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C?blocks_apart_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB;after_new_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbLGC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z8sub_diagC46Stdlib6ZArith4Zdiv8Zmod_0_lC56Stdlib6ZArith6BinInt1Z:div_uniqueC56Stdlib6ZArith6BinInt1Z6mod_eqC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbL0_concC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB8cnd_evalC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6cnd_neC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB7tail_LIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6cnd_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6grow_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbL0_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<KS_ad_pbL0_1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6grow_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6path_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB6path_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSPb6PQADPB7pb_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7pb_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADPB.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) [] (Mh_0188_blobs1.kr_b_247 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o ch S r SM g : Z) (x : PM.vstr).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 ch.
Hypothesis Hch : 0 <= ch < 256.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis Hroom : PM.vs_size x < SM.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + 1 ->
  L5C.hpres L LB S 14336 [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_248 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_249 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14336 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14336 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_250 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_251 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (x' : PM.vstr) (g' : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  kstr_at M1 o x' -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + 1 -> mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') -> model_but_vm model0 model1 ->
  hi_heap HI (PM.vs_own x' ++ LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66574 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_252 ())). Qed.

(* [comment removed for export] *)
Lemma cs_back (R1 : bvmap 5 word) (KS : list nat) :
  (forall k, In k KS -> getr R1 (reg k) = getr R0 (reg k)) -> forallb (fun k => existsb (Nat.eqb k) KS) PMK.cs_all = true ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_253 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land2_0 n : 0 <= n <= 21 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_254 ())). Qed.

Lemma path_S (n : Z) : x = PM.VShort n -> n <= 21 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_255 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 64 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_256 ())). Qed.

Lemma tail_LI (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c n p : Z) :
  x = PM.VLong c n p -> n < c - 1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 20) = Z_to_bv 64 n -> kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66538 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_257 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_258 ())). Qed.

Lemma tail_F (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 19) = Z_to_bv 64 A -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 22) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> PM.vs_size x + 1 < A ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x6652c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_259 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_T (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 19) = Z_to_bv 64 A -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 21) = Z_to_bv 64 23 ->
  getr R1 (reg 22) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> PM.vs_size x + 1 < A ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66518 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_260 ())). Qed.

Lemma tail_D (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c p A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VLong c (c - 1) p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 p -> getr R1 (reg 19) = Z_to_bv 64 A -> getr R1 (reg 20) = Z_to_bv 64 (c - 1) ->
  getr R1 (reg 21) = Z_to_bv 64 c -> getr R1 (reg 22) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> c < A -> B <> p ->
  hi_heap HI ((B, A) :: (p, c) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A c B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A c B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66518 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_261 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_new_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VShort 22 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 B -> getr R1 (reg 18) = Z_to_bv 64 (o + 1) -> getr R1 (reg 19) = Z_to_bv 64 48 ->
  getr R1 (reg 20) = Z_to_bv 64 22 -> getr R1 (reg 21) = Z_to_bv 64 23 ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B 48 -> 4096 <= B -> B + 48 <= hl_ceil L ->
  hi_heap HI ((B, 48) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong 48 23 B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong 48 23 B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66508 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_262 ())). Qed.

Lemma after_new_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c p A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VLong c (c - 1) p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 B -> getr R1 (reg 18) = Z_to_bv 64 p -> getr R1 (reg 19) = Z_to_bv 64 A ->
  getr R1 (reg 20) = Z_to_bv 64 (c - 1) -> getr R1 (reg 21) = Z_to_bv 64 c ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> c < A ->
  L5.defined M1 p c -> 4096 <= p -> p + c <= hl_ceil L -> (B + A <= p \/ p + c <= B) ->
  hi_heap HI ((B, A) :: (p, c) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A c B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A c B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66508 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_263 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_ok_callee M1 M3 LBc scr :
  mem_ok M1 -> L5C.hpres L LBc (S - 64) scr [] M1 M3 -> incl LB LBc -> PMFR.brange L LBc -> 0 <= scr -> 64 + scr <= 14336 ->
  L5C.stk (hl_sptop L) M1 (S - 64) scr -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_264 ())). Qed.

Lemma saves_callee M1 M3 LBc scr :
  saves M1 -> L5C.hpres L LBc (S - 64) scr [] M1 M3 -> 0 <= scr -> L5C.stk (hl_sptop L) M1 (S - 64) scr -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_265 ())). Qed.

Lemma stk_new M1 : mem_ok M1 -> L5C.stk (hl_sptop L) M1 (S - 64) PMSP.OPNEW_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_266 ())). Qed.

(* [comment removed for export] *)
Lemma grow_S : x = PM.VShort 22 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_267 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c p : Z) :
  x = PM.VLong c (c - 1) p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (c - 1) -> getr R1 (reg 20) = Z_to_bv 64 (c - 1) -> getr R1 (reg 21) = Z_to_bv 64 c ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x664ac M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_268 ())). Qed.

(* [comment removed for export] *)
Lemma cnd_eval c n : 26 <= c <= 2 ^ 31 -> c mod 2 = 0 -> 0 <= n < c ->
  ((n - ((((2 * (c / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) = (n - (c - 1)) mod 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_269 ())). Qed.
Lemma cnd_ne c n : 26 <= c <= 2 ^ 31 -> 0 <= n < c -> 1 <= (n - (c - 1)) mod 2 ^ 64 -> n < c - 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_270 ())). Qed.
Lemma cnd_eq c n : 26 <= c <= 2 ^ 31 -> 0 <= n < c -> (n - (c - 1)) mod 2 ^ 64 < 1 -> n = c - 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_271 ())). Qed.

(* [comment removed for export] *)
Lemma path_L (c n p : Z) : x = PM.VLong c n p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_272 ())). Qed.

(* [comment removed for export] *)
Lemma pb_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_273 ())). Qed.

End Call.

Theorem pb_ok : PQAS.pb_spec RSEGS AD L HI 0x66444.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPb ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_274 ())). Qed.

End WithHeap.
End PQADPB.

End PnAdSPb.
From Stdlib Require ZArith List Lia Bool Permutation FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.
Module PnAdVKitN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnMpKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnMpBaKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSIns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdLvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdVKitN () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5lv_eoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3advC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init5Logic3and01K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega6VarMap1t03C47Corelib4Init5Logic3notK69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lv_rootC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List8app_nth2I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Peano2ltC47Corelib4Init3Nat3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3subC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelc69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6adv_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01429PnAdLvKit4PQLKAlv_shape_set_lastC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lv_shapeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_geC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_01028PnQModel3PQM9MAX_DEPTHC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK8adv_rootC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib7Sorting;Permutation?Permutation_symI35stdpp4base5NoDup00I46Stdlib5Lists4List5NoDup00C35stdpp4base?NoDup_ListNoDupC47Corelib4Init9Datatypes3fstC46Stdlib7Sorting;Permutation?Permutation_mapC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK:heap_nodupC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupC59OSSVerify5KrLib7Mh_00849HeapIface8hio_permC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_01028PnQModel3PQM9adaptor_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5enc_WC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5err_WC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS<opnew_spec_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opdel_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS4NREQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6ctx_okC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ASIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2cmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?inW_not_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3IMGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK7inW_adWC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6ek_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01356PmStep3PMK;client_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C:hpres_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffc69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK5inW_AC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK5worldC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout8pa_rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFRBoutside_of_not_inWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_canaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_need_locksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_locale_lockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP<base_ok_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK:world_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3HDRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3KEYC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2KBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lvec_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_LVC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF8vs_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF3dkrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF<kstr_at_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9kstr_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0102>PnMpModelFacts4PQMF=lvec_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8pow2_posC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01429PnAdLvKit4PQLK=lvec_set_lastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lvec_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationHPermutation_app_swap_appC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:pot_vstackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01429PnMpBaKit4PQBKApot_vstack_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS=pot_ks_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM;pot_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsc69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK8ad_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK7perm_kbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9heap_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9pot_partsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9cle_add_lC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7pb_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6m8_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;dk_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5ag_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6inW_kbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9cm_calleeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS8ly_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6ag_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK7LV_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK7ad_joinC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_add_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK8perm_keyC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9cle_add_rC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_01426PnKitS4PMKS9cstatic_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP<kept_cstaticC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9world_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7rdn_imgC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6src_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ins_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK=after_strcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29img_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP:kept_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove4PMCP>rdn_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP:kept_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNADVK.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation AQ := PnLayoutQS.QADDR_S.
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation lvec_at := (PQM.lvec_at RSEGS PMSP.T3 PMSP.T4).
Abbreviation alvl_at := (PQM.alvl_at RSEGS).
Abbreviation adaptor_at := (PQM.adaptor_at RSEGS AD PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_275 ())). Qed.
Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_276 ())). Qed.
Lemma reg_back (R R' : bvmap 5 word) k k' : getr R' (reg k') = Z_to_bv 64 (bv_unsigned (getr R (reg k))) -> getr R' (reg k') = getr R (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_277 ())). Qed.
Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_278 ())). Qed.
Lemma G64 (R : bvmap 5 word) x : 0 <= bv_unsigned (getr R (reg x)) < 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_279 ())). Qed.

(* [comment removed for export] *)
Definition adv (c : PQM.alvl) : PQM.alvl :=
  PQM.AL (PQM.lv_t c) (PQM.lv_k c) (if Z.eqb (PQM.lv_k c) 2 then 1 - PQM.lv_eo c else PQM.lv_eo c).
Lemma adv_ok c : PQM.alvl_ok c -> PQM.alvl_ok (adv c).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_280 ())). Qed.
Lemma adv_root : adv PQM.lv_root = PQM.lv_root.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_281 ())). Qed.
Lemma lv_shape_adv lv0 c : PQM.lv_shape (lv0 ++ [c]) -> PQM.lv_shape (lv0 ++ [adv c]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) [] (Mh_0188_blobs1.kr_b_282 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.
Let PB := PQADPB.pb_ok L HI LY HIok OPN OPD.
Let INSW := PQADINS.ins_ok L HI LY HIok OPN OPD.
Let INSC := PQADJNS.ins_ok L HI LY HIok OPN OPD.

Lemma heap_perm l1 l2 cr M VM : Permutation l1 l2 -> hi_heap HI l1 cr M VM -> hi_heap HI l2 cr M VM.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_283 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ctx.
Variables (M0 : word -> option byte) (K : TSet) (LBX : list (Z * Z)) (S oa ov osk oec : Z).
(* [comment removed for export] *)
Definition ctx_ok : Prop :=
  K [] /\ L5C.stk (hl_sptop L) M0 S 28672 /\ S <= oa /\ oa + PQM.ASIZE <= hl_sptop L /\ oa mod 8 = 0 /\ S <= ov /\ ov + 56 <= hl_sptop L /\ oa + PQM.ASIZE <= ov
  /\ L5.u64_at RSEGS M0 ov (ne_vt NemLayoutS.NEADDR_S) /\ PMST.base_ok RSEGS AD M0 /\ PMFR.brange L LBX.
Hypothesis CX : ctx_ok.
Local Ltac ctx := pose proof LY as LY'; pose proof HIok as HIok'; pose proof OPN as OPN'; pose proof OPD as OPD';
  pose proof CX as (K0 & STK0 & Ho1 & Ho2 & Ho3 & Hov1 & Hov2 & Hov3 & VIS0 & BASE0 & BRX).

(* [comment removed for export] *)
#[local] Abbreviation WA := (NEM.ae_W AD oa ov osk oec).
Definition cm (M : word -> option byte) : Prop :=
  PMK.ek L LBX S 28672 WA M0 M /\ PMK.dk L LBX S 28672 M0 M /\ L5C.stk (hl_sptop L) M S 28672.
Definition world (M : word -> option byte) : Prop := L5.u64_at RSEGS M ov (ne_vt NemLayoutS.NEADDR_S) /\ PMST.base_ok RSEGS AD M.
Lemma inW_adW a : PMK.inW (PQM.adaptor_W oa) a -> PMK.inW WA a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_284 ())). Qed.
Definition HDR (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M oa (qa_vp_adaptor AQ) /\ L5.u64_at RSEGS M (oa + 8) (pa_vp_visitor AD) /\ L5.u64_at RSEGS M (oa + 16) ov /\ L5.defined M oa 96.
Definition KEY (M : word -> option byte) (kx : PM.vstr) : Prop := kstr_at M (oa + 24) kx.
Definition KB (M : word -> option byte) (kb2 : PM.vstr) : Prop := kstr_at M (oa + 48) kb2.
Definition LV (M : word -> option byte) (bX kX : Z) (lv2 : list PQM.alvl) : Prop := lvec_at M (oa + 72) bX kX lv2.

Lemma frame0 : 0x7fff7f800000 + 28672 <= S /\ S mod 16 = 0 /\ hl_ceil L + 28672 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_285 ())). Qed.
Lemma IMG : hl_img_lo L = 0x10000 /\ hl_img_hi L = 0xfa000.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_286 ())). Qed.

Lemma cm0 : cm M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_287 ())). Qed.
Lemma cm_hpres M : cm M -> L5C.hpres L LBX S 28672 WA M0 M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_288 ())). Qed.

(* [comment removed for export] *)
Lemma ek_frz LBc W' M1 M2 (P : Z -> Prop) :
  PMFR.brange L LBc ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> (S - 28672 <= a < S) \/ PMK.inW W' a \/ (a < hl_ceil L /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ ~ in_block LBc a)) ->
  PMK.ek L LBc S 28672 W' M1 M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_289 ())). Qed.
Lemma cm_frz M1 M2 (P : Z -> Prop) : cm M1 -> mem_grows M1 M2 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> (S - 28672 <= a < S) \/ PMK.inW (PQM.adaptor_W oa) a \/ (a < hl_ceil L /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ ~ in_block LBX a)) ->
  cm M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_290 ())). Qed.
(* [comment removed for export] *)
Lemma cm_callee LBc sp' scr' W' M1 M2 :
  cm M1 -> L5C.hpres L LBc sp' scr' W' M1 M2 -> incl LBX LBc -> S - 28672 <= sp' - scr' -> sp' <= S -> 0 <= scr' ->
  (forall a, PMK.inW W' a -> PMK.inW WA a) -> cm M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_291 ())). Qed.
Lemma inW_A a : PMK.inW (PQM.adaptor_W oa) a <-> oa + 24 <= a < oa + 96.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_292 ())). Qed.
(* [comment removed for export] *)

Lemma inW_kb a : PMK.inW [(oa + 48, 24)] a -> PMK.inW (PQM.adaptor_W oa) a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_293 ())). Qed.
Lemma inW_key a : PMK.inW [(oa + 24, 24)] a -> PMK.inW (PQM.adaptor_W oa) a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_294 ())). Qed.

(* [comment removed for export] *)
Lemma world_keep LBc sp' scr' W' M1 M2 :
  PMK.ek L LBc sp' scr' W' M1 M2 -> L5C.stk (hl_sptop L) M1 sp' scr' -> 0 <= scr' -> sp' <= S ->
  (forall a, PMK.inW W' a -> PMK.inW (PQM.adaptor_W oa) a) -> world M1 -> world M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_295 ())). Qed.
Lemma world0 : world M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_296 ())). Qed.
(* [comment removed for export] *)
Lemma world_frz M1 M2 (P : Z -> Prop) :
  L5C.stk (hl_sptop L) M1 S 28672 ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> (S - 28672 <= a < S) \/ (oa + 24 <= a < oa + 96) \/ (a < hl_ceil L /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ ~ in_block LBX a)) ->
  world M1 -> world M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_297 ())). Qed.
(* [comment removed for export] *)
Lemma world_img M : world M -> L5.img_clear M 65536 814272.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_298 ())). Qed.
Lemma world_vis M : world M -> L5.u64_at RSEGS M ov 785968.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_299 ())). Qed.


(* [comment removed for export] *)
Lemma ad_split M lv2 bX kX kx kgx kb2 g2 : adaptor_at M oa ov (PQM.AST lv2 bX kX kx kgx kb2 g2) -> HDR M /\ KEY M kx /\ KB M kb2 /\ LV M bX kX lv2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_300 ())). Qed.
Lemma ad_join M lv2 bX kX kx kgx kb2 g2 : HDR M -> KEY M kx -> KB M kb2 -> LV M bX kX lv2 -> adaptor_at M oa ov (PQM.AST lv2 bX kX kx kgx kb2 g2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_301 ())). Qed.
Lemma HDR_keep M1 M2 : mem_grows M1 M2 -> L5C.agree_on M1 M2 oa 24 -> HDR M1 -> HDR M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_302 ())). Qed.
Lemma kstr_keep M1 M2 o x : 0 <= o -> o + 24 <= 2 ^ 64 -> mem_grows M1 M2 -> L5C.agree_on M1 M2 o 24 -> kstr_at M1 o x -> kstr_at M2 o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_303 ())). Qed.
Lemma KEY_keep M1 M2 kx : mem_grows M1 M2 -> L5C.agree_on M1 M2 (oa + 24) 24 -> KEY M1 kx -> KEY M2 kx.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_304 ())). Qed.
Lemma KB_keep M1 M2 kb2 : mem_grows M1 M2 -> L5C.agree_on M1 M2 (oa + 48) 24 -> KB M1 kb2 -> KB M2 kb2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_305 ())). Qed.
Lemma LV_keep M1 M2 bX kX lv2 : 0 <= bX -> bX + 24 * 2 ^ kX <= 2 ^ 64 -> L5C.agree_on M1 M2 (oa + 72) 24 -> L5C.agree_on M1 M2 bX (24 * 2 ^ kX) -> LV M1 bX kX lv2 -> LV M2 bX kX lv2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_306 ())). Qed.
(* [comment removed for export] *)
Lemma LV_set_last M1 M2 bX kX lv0 c c' (e : Z) : LV M1 bX kX (lv0 ++ [c]) -> e = bX + 24 * (Z.of_nat (length lv0) + 1) -> mem_grows M1 M2 ->
  0 <= bX -> bX + 24 * 2 ^ kX <= hl_ceil L ->
  L5C.agree_on M1 M2 (oa + 72) 24 -> L5C.agree_on M1 M2 bX (24 * Z.of_nat (length lv0)) -> L5C.agree_on M1 M2 (e - 24) 8 ->
  PQM.lv_t c' = PQM.lv_t c -> PQM.lv_k c' = PQM.lv_k c -> L5.u32_at RSEGS M2 (e - 16) (PQM.lv_eo c') -> LV M2 bX kX (lv0 ++ [c']).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_307 ())). Qed.
(* [comment removed for export] *)
Lemma top_cells M1 bX kX lv0 c (e : Z) : LV M1 bX kX (lv0 ++ [c]) -> e = bX + 24 * (Z.of_nat (length lv0) + 1) ->
  L5.u64_at RSEGS M1 (oa + 72) bX /\ L5.u64_at RSEGS M1 (oa + 80) e /\ L5.u64_at RSEGS M1 (oa + 88) (bX + 24 * 2 ^ kX)
  /\ L5.u32_at RSEGS M1 (e - 24) (PQM.lv_t c) /\ L5.u32_at RSEGS M1 (e - 20) (PQM.lv_k c) /\ L5.u32_at RSEGS M1 (e - 16) (PQM.lv_eo c) /\ L5.defined M1 (e - 24) 24
  /\ L5.defined M1 bX (24 * 2 ^ kX) /\ 0 <= kX <= 11 /\ Z.of_nat (length lv0) + 1 <= 2 ^ kX /\ bX mod 16 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_308 ())). Qed.

(* [comment removed for export] *)
Lemma perm_kb lvX bX kX kx kgx kbx gx : Permutation (PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx) ++ LBX) (PM.vs_own kbx ++ (PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_309 ())). Qed.
Lemma perm_key lvX bX kX kx kgx kbx gx : Permutation (PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx) ++ LBX) (PM.vs_own kx ++ (PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_310 ())). Qed.
(* [comment removed for export] *)
Lemma pot_parts lvX bX kX kx kgx kbx gx : 0 <= kX <= 11 -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx ->
  0 <= fst (PQM.pot_vstack L kX) /\ 0 <= snd (PQM.pot_vstack L kX) /\ 0 <= fst (PQM.pot_ks L PQM.SMK kx kgx) /\ 0 <= snd (PQM.pot_ks L PQM.SMK kx kgx)
  /\ 0 <= fst (PQM.pot_ks L PQM.SMB kbx gx) /\ 0 <= snd (PQM.pot_ks L PQM.SMB kbx gx)
  /\ PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx) = PM.credit_add (PQM.pot_vstack L kX) (PM.credit_add (PQM.pot_ks L PQM.SMK kx kgx) (PQM.pot_ks L PQM.SMB kbx gx)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_311 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma PBCALL (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kb1 : PM.vstr) (g1 : Z) (cr : credit) (ra ch : Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 48) -> getr R (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 256 ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kb1 g1) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kb1 g1 -> PM.vs_size kb1 < PQM.SMB ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb1 g1) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kb2 : PM.vstr) (g2 : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 48 \/ oa + 72 <= a) -> L5C.agree_on M M' a m) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx kgx kb2 g2) -> PQM.ks_ok PQM.SMB kb2 g2 -> PM.vs_size kb2 = PM.vs_size kb1 + 1 ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb2 g2)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb2 g2) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x66444 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_312 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_strcall (sp' wlo : Z) (M M' : word -> option byte) (LBs : list (Z * Z)) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z)
      (kx' : PM.vstr) (kgx' : Z) (kbx' : PM.vstr) (gx' : Z) (cr : credit) (VM : VmMaps) :
  (wlo = oa + 24 /\ kbx' = kbx /\ LBs = PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX /\ KEY M' kx') \/ (wlo = oa + 48 /\ kx' = kx /\ LBs = PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX /\ KB M' kbx') ->
  S - 4096 <= sp' -> sp' <= S -> L5C.stk (hl_sptop L) M sp' WD.PB_SCR -> PMFR.brange L LBs ->
  L5C.hpres L LBs sp' WD.PB_SCR [(wlo, 24)] M M' -> cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kbx gx) ->
  cm M' /\ world M' /\ (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= wlo \/ wlo + 24 <= a) -> L5C.agree_on M M' a m)
  /\ adaptor_at M' oa ov (PQM.AST lvX bX kX kx' kgx' kbx' gx').
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_313 ())). Qed.

(* [comment removed for export] *)
Lemma after_strcall_scr (scr sp' wlo : Z) (M M' : word -> option byte) (LBs : list (Z * Z)) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z)
      (kx' : PM.vstr) (kgx' : Z) (kbx' : PM.vstr) (gx' : Z) (cr : credit) (VM : VmMaps) :
  (wlo = oa + 24 /\ kbx' = kbx /\ LBs = PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX /\ KEY M' kx') \/ (wlo = oa + 48 /\ kx' = kx /\ LBs = PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX /\ KB M' kbx') ->
  0 <= scr -> S - 28672 <= sp' - scr -> sp' <= S -> L5C.stk (hl_sptop L) M sp' scr -> PMFR.brange L LBs ->
  L5C.hpres L LBs sp' scr [(wlo, 24)] M M' -> cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kbx gx) ->
  cm M' /\ world M' /\ (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= wlo \/ wlo + 24 <= a) -> L5C.agree_on M M' a m)
  /\ adaptor_at M' oa ov (PQM.AST lvX bX kX kx' kgx' kbx' gx').
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_314 ())). Qed.

(* [comment removed for export] *)
Lemma INSKEY (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kbx : PM.vstr) (gx : Z) (cr : credit) (ra q n : Z) (zs : list Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 24) -> getr R (reg 11) = Z_to_bv 64 (PM.vs_data (oa + 24) kx + PM.vs_size kx) ->
  getr R (reg 12) = Z_to_bv 64 q -> getr R (reg 13) = Z_to_bv 64 (q + n) -> getr R (reg 14) = Z_to_bv 64 n ->
  0 <= n -> PM.vs_size kx + n <= PQM.SMK -> 0x10000 <= q -> q + n <= 0xc6cc0 -> AX2.img_bytes RSEGS q (Z.to_nat n) = Some zs -> length zs = Z.to_nat n ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kbx gx) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kx' : PM.vstr) (kgx' : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 24 \/ oa + 48 <= a) -> L5C.agree_on M M' a m) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx' kgx' kbx gx) -> PQM.ks_ok PQM.SMK kx' kgx' -> PM.vs_size kx' = PM.vs_size kx + n ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx' kgx' kbx gx)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx' kgx' kbx gx) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3e908 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_315 ())). Qed.

(* [comment removed for export] *)
Lemma PBKEY (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kbx : PM.vstr) (gx : Z) (cr : credit) (ra ch : Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 24) -> getr R (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 256 ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kbx gx) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kx < PQM.SMK ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kx' : PM.vstr) (kgx' : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 24 \/ oa + 48 <= a) -> L5C.agree_on M M' a m) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx' kgx' kbx gx) -> PQM.ks_ok PQM.SMK kx' kgx' -> PM.vs_size kx' = PM.vs_size kx + 1 ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx' kgx' kbx gx)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx' kgx' kbx gx) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x66444 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_316 ())). Qed.

(* [comment removed for export] *)
Lemma INSKB (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kb1 : PM.vstr) (g1 : Z) (cr : credit) (ra : Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 48) -> getr R (reg 11) = Z_to_bv 64 (PM.vs_data (oa + 48) kb1 + PM.vs_size kb1) ->
  getr R (reg 12) = Z_to_bv 64 (PM.vs_data (oa + 24) kx) -> getr R (reg 13) = Z_to_bv 64 (PM.vs_data (oa + 24) kx + PM.vs_size kx) -> getr R (reg 14) = Z_to_bv 64 (PM.vs_size kx) ->
  PM.vs_size kb1 + PM.vs_size kx <= PQM.SMB ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kb1 g1) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kb1 g1 ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb1 g1) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kb2 : PM.vstr) (g2 : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 48 \/ oa + 72 <= a) -> L5C.agree_on M M' a m) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx kgx kb2 g2) -> PQM.ks_ok PQM.SMB kb2 g2 -> PM.vs_size kb2 = PM.vs_size kb1 + PM.vs_size kx ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb2 g2)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb2 g2) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3ccec M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdVKitN ()) ["WithHeap"; "Ctx"] (Mh_0188_blobs1.kr_b_317 ())). Qed.

End Ctx.
End WithHeap.
End PNADVK.

End PnAdVKitN.
Module PnAdSPbS2P.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.

Module PQADPBS2P.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
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
Module Pad_pbS2 := BndP_Ns_036.LibSegNs_ad_pbS2.
Definition KS_ad_pbS2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_pbS2.regs0 Pad_pbS2.regs_out0).
Lemma KS_ad_pbS2_ok : BG.kept_ok 64 Pad_pbS2.regs0 Pad_pbS2.regs_out0 KS_ad_pbS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ad_pbS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> 0 <= (bv_unsigned (getr R (reg 11))) <= 255 ->
  L5.u8_at RSEGS M (bv_unsigned (getr R (reg 10))) (2 * (V 34%nat)) -> 0 <= (V 34%nat) <= 21 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 1) -> ~ ((((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1) <= bv_unsigned a < (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 1) -> ~ ((((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1) <= i < (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x66444 M) (st fx' R' 0x66574 M')
        /\ (forall x, In x KS_ad_pbS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((2 * (V 34%nat)) + 2)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 2) 0
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 10))) + (V 34%nat)) + 1) (bv_unsigned (getr R (reg 11)))
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 10))) ((2 * (V 34%nat)) + 2)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 pvzI3 K1 K2 pvzI4 K4 K5 K6 pvzI5 K8 pvzI6 K10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K7l; move K7l before pvzI5; pose proof (proj2 pvzI5) as K7r; move K7r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K9l; move K9l before pvzI6; pose proof (proj2 pvzI6) as K9r; move K9r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E Pad_pbS2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pad_pbS2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pad_pbS2.kn0).
  { unfold know_ok, Pad_pbS2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear) | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r K9l K9r) | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | byte_tac ltac:(clear - HV34l HV34r K9l K9r) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K10]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pad_pbS2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pad_pbS2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 1) -> ~ ((((bv_unsigned (getr R (reg 10))) + vz_34) + 1) <= bv_unsigned a < (((bv_unsigned (getr R (reg 10))) + vz_34) + 1) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pad_pbS2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K9l K9r) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K5 HV34l HV34r K9l K9r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pad_pbS2.ps0) with 0x66574 in Hms. change (SR.ps_regs Pad_pbS2.ps0) with (map (fun i => (i, nth i Pad_pbS2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pad_pbS2.ps0) with Pad_pbS2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pad_pbS2.regs0 Pad_pbS2.regs_out0 64 KS_ad_pbS2 KS_ad_pbS2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pad_pbS2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pad_pbS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_pbS2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pad_pbS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K9l K9r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K9l K9r) | evalEk' ZA Hag ltac:(clear - K7l K7r) | byte_tac ltac:(clear - K7l K7r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K9l K9r) | byte_tac ltac:(clear - HV34l HV34r K9l K9r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PQADPBS2P.

End PnAdSPbS2P.
Module PnAdSPbC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPbP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPbS2P OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r62890_62894.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSPbC () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdC69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List:length_appK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC=bytes_at_snocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<bytes_ok_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC3KCFC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppI47Corelib4Init5Logic4True00c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC3BRXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62890_628947W_6652cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62890_628947F_6652cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62890_628947D_6652cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6sub_inC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallK69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188:PnAdSPbS2P9PQADPBS2P<ad_pbS2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188:PnAdSPbS2P9PQADPBS2P7alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7land2_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC<mem_ok_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7cs_backC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7kc_snocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188:PnAdSPbS2P9PQADPBS2P:KS_ad_pbS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7mem_ok0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC5kept0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbT_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6tail_FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbTC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbD_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opdel_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR7inW_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR<defined_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP;ad_pbM_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<memmove_runCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC;saves_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6tail_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP9KS_ad_pbMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6tail_DC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPNEW_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbSG_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ks_growC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS;pot_ks_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7stk_newC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS<opnew_spec_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;fresh_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBfresh_block_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC<saves_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC=mem_ok_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK5ag_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC;after_new_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbSGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS4NREQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP<ad_pbLG_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9gcount_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C?blocks_apart_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC;after_new_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbP7PQADPBP:KS_ad_pbLGC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC56Stdlib6ZArith6BinInt1Z6eq_decC56Stdlib6ZArith6BinInt1Z8sub_diagC46Stdlib6ZArith4Zdiv8Zmod_0_lC56Stdlib6ZArith6BinInt1Z:div_uniqueC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6mod_eqK47Corelib4Init5Logic2ex01c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6grow_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6path_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC6path_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSPbC7PQADPBC7pb_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC8pb_specCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADPBC.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation kcontent := (NEM.kcontent RSEGS).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) [] (Mh_0188_blobs1.kr_b_318 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o ch S r SM g : Z) (x : PM.vstr) (bs : list Z).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 ch.
Hypothesis Hch : 0 <= ch < 256.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KC0 : kcontent M0 o x bs.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis Hroom : PM.vs_size x < SM.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> kcontent M' o x' (bs ++ [ch]) -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + 1 ->
  L5C.hpres L LB S 14336 [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

(* [comment removed for export] *)
Lemma KCF : L5.bytes_at RSEGS M0 (PM.vs_data o x) bs /\ NEM.bytes_ok bs /\ Z.of_nat (length bs) = PM.vs_size x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_319 ())). Qed.
(* [comment removed for export] *)
Lemma kc_snoc M d x' : PM.vs_data o x' = d -> PM.vs_size x' = PM.vs_size x + 1 ->
  L5.bytes_at RSEGS M d bs -> L5.u8_at RSEGS M (PM.vs_size x + d) ch -> kcontent M o x' (bs ++ [ch]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_320 ())). Qed.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_321 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_322 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14336 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14336 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_323 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_324 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (x' : PM.vstr) (g' : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  kstr_at M1 o x' -> kcontent M1 o x' (bs ++ [ch]) -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + 1 -> mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') -> model_but_vm model0 model1 ->
  hi_heap HI (PM.vs_own x' ++ LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66574 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_325 ())). Qed.

(* [comment removed for export] *)
Lemma cs_back (R1 : bvmap 5 word) (KS : list nat) :
  (forall k, In k KS -> getr R1 (reg k) = getr R0 (reg k)) -> forallb (fun k => existsb (Nat.eqb k) KS) PMK.cs_all = true ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_326 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land2_0 n : 0 <= n <= 21 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_327 ())). Qed.

Lemma path_S (n : Z) : x = PM.VShort n -> n <= 21 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_328 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 64 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_329 ())). Qed.

Lemma tail_LI (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c n p : Z) :
  x = PM.VLong c n p -> n < c - 1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 20) = Z_to_bv 64 n -> kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 p bs ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66538 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_330 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_331 ())). Qed.

Lemma tail_F (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 19) = Z_to_bv 64 A -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 22) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> PM.vs_size x + 1 < A ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x6652c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_332 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_T (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 19) = Z_to_bv 64 A -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 21) = Z_to_bv 64 23 ->
  getr R1 (reg 22) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> PM.vs_size x + 1 < A ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (PM.vs_size x + 1) B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66518 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_333 ())). Qed.

Lemma tail_D (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c p A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VLong c (c - 1) p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 p -> getr R1 (reg 19) = Z_to_bv 64 A -> getr R1 (reg 20) = Z_to_bv 64 (c - 1) ->
  getr R1 (reg 21) = Z_to_bv 64 c -> getr R1 (reg 22) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> c < A -> B <> p ->
  hi_heap HI ((B, A) :: (p, c) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A c B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A c B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66518 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_334 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_new_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VShort 22 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 B -> getr R1 (reg 18) = Z_to_bv 64 (o + 1) -> getr R1 (reg 19) = Z_to_bv 64 48 ->
  getr R1 (reg 20) = Z_to_bv 64 22 -> getr R1 (reg 21) = Z_to_bv 64 23 ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> L5.bytes_at RSEGS M1 (o + 1) bs ->
  L5.defined M1 B 48 -> 4096 <= B -> B + 48 <= hl_ceil L ->
  hi_heap HI ((B, 48) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong 48 23 B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong 48 23 B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66508 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_335 ())). Qed.

Lemma after_new_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c p A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VLong c (c - 1) p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 B -> getr R1 (reg 18) = Z_to_bv 64 p -> getr R1 (reg 19) = Z_to_bv 64 A ->
  getr R1 (reg 20) = Z_to_bv 64 (c - 1) -> getr R1 (reg 21) = Z_to_bv 64 c ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> 48 <= A <= PQM.KCAP -> A mod 8 = 0 -> c < A ->
  L5.bytes_at RSEGS M1 p bs -> L5.defined M1 p c -> 4096 <= p -> p + c <= hl_ceil L -> (B + A <= p \/ p + c <= B) ->
  hi_heap HI ((B, A) :: (p, c) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PQM.ks_ok SM (PM.VLong A c B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A c B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66508 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_336 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mem_ok_callee M1 M3 LBc scr :
  mem_ok M1 -> L5C.hpres L LBc (S - 64) scr [] M1 M3 -> incl LB LBc -> PMFR.brange L LBc -> 0 <= scr -> 64 + scr <= 14336 ->
  L5C.stk (hl_sptop L) M1 (S - 64) scr -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_337 ())). Qed.

Lemma saves_callee M1 M3 LBc scr :
  saves M1 -> L5C.hpres L LBc (S - 64) scr [] M1 M3 -> 0 <= scr -> L5C.stk (hl_sptop L) M1 (S - 64) scr -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_338 ())). Qed.

Lemma stk_new M1 : mem_ok M1 -> L5C.stk (hl_sptop L) M1 (S - 64) PMSP.OPNEW_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_339 ())). Qed.

(* [comment removed for export] *)
Lemma grow_S : x = PM.VShort 22 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_340 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c p : Z) :
  x = PM.VLong c (c - 1) p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 ch -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (c - 1) -> getr R1 (reg 20) = Z_to_bv 64 (c - 1) -> getr R1 (reg 21) = Z_to_bv 64 c ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 p bs ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x664ac M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_341 ())). Qed.

(* [comment removed for export] *)
Lemma cnd_eval c n : 26 <= c <= 2 ^ 31 -> c mod 2 = 0 -> 0 <= n < c ->
  ((n - ((((2 * (c / 2)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)) mod 2 ^ 64) = (n - (c - 1)) mod 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_342 ())). Qed.
Lemma cnd_ne c n : 26 <= c <= 2 ^ 31 -> 0 <= n < c -> 1 <= (n - (c - 1)) mod 2 ^ 64 -> n < c - 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_343 ())). Qed.
Lemma cnd_eq c n : 26 <= c <= 2 ^ 31 -> 0 <= n < c -> (n - (c - 1)) mod 2 ^ 64 < 1 -> n = c - 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_344 ())). Qed.

(* [comment removed for export] *)
Lemma path_L (c n p : Z) : x = PM.VLong c n p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_345 ())). Qed.

(* [comment removed for export] *)
Lemma pb_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x66444 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_346 ())). Qed.

End Call.

Theorem pb_ok : PQASC.pb_specC RSEGS AD L HI 0x66444.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSPbC ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_347 ())). Qed.

End WithHeap.
End PQADPBC.

End PnAdSPbC.
Module PnAdSGbC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGbP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r62758_6275c.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSGbC () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr03C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6GB_SCRC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ks_growC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6cap_geC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9gcount_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3divc69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC3BRXC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR7inW_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR<defined_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR5ag_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC=kstr_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPNEW_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC3KCFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC8x_cases'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC8growth_BC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6growthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62758_6275c7W_663f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62758_6275c7F_663f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r62758_6275c7D_663f4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC5reg_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;ad_gbF_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP7alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC<mem_ok_frameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6cs_finC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC;size_le_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP9KS_ad_gbFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbTs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP:KS_ad_gbTsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbTd_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS:opdel_specC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC<saves_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC=mem_ok_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6tail_FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP:KS_ad_gbTdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9OPDEL_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7tail_TsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7tail_TdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7x_casesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;ad_gbN_concC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C56Stdlib6ZArith6BinInt1Z7sub_0_rC69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<memmove_runCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC;saves_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC6at_648C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;KS_ad_gbN_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;KS_ad_gbN_1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specc69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP;ad_gbR_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS;pot_ks_growC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface5debitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7stk_newC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS<opnew_spec_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;fresh_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBfresh_block_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_applc69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC;kstr_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC<bytes_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C?blocks_apart_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC9after_newC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP9KS_ad_gbRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC8alloc_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC4A_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS4NREQC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<ad_gbEs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7land2_0C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC;bytes_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC4growC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEs_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbP7PQADGBP<KS_ad_gbEs_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7mem_ok0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7entry_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7entry_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01888PnAdSGbC7PQADGBC7gb_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC8gb_specCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC6GB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADGBC.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) [] (Mh_0188_blobs1.kr_b_348 ())). Qed.

Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) [] (Mh_0188_blobs1.kr_b_349 ())). Qed.

Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) [] (Mh_0188_blobs1.kr_b_350 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_at_agree (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> L5C.agree_on M M' o 24 -> (forall c n p, x = PM.VLong c n p -> L5C.agree_on M M' p c) ->
  kstr_at M o x -> kstr_at M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) [] (Mh_0188_blobs1.kr_b_351 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.

(* [comment removed for export] *)
Definition GB_SCR : Z := 14272.

(* [comment removed for export] *)
Definition gb_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o need sp r SM g : Z) (x : PM.vstr),
    hi_heap HI (PM.vs_own x ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp AD) ->
    L5C.stk (hl_sptop L) M sp GB_SCR ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 (PM.vs_cap x) -> getr R 12%bv = Z_to_bv 64 (need - PM.vs_cap x) ->
    getr R 13%bv = Z_to_bv 64 (PM.vs_size x) -> getr R 14%bv = Z_to_bv 64 (PM.vs_size x) -> getr R 15%bv = Z_to_bv 64 0 ->
    kstr_at M o x -> PQM.ks_ok SM x g -> SM <= PQAS.SMMAX -> PM.vs_cap x < need <= SM ->
    sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    PMSP.credit_le (PQM.pot_ks L SM x g) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B A : Z) (cr' : credit),
        regs_preserved R R' -> A = PQAS.gcount (PM.vs_cap x) need ->
        L5.defined M' o 24 -> L5.u64_at RSEGS M' o (A + 1) -> L5.u64_at RSEGS M' (o + 16) B ->
        L5.defined M' B A -> 4096 <= B -> B + A <= hl_ceil L ->
        PQM.ks_ok SM (PM.VLong A need B) (g + 1) -> need < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
        L5C.hpres L LB sp GB_SCR [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
        model_but_vm model model' -> hi_heap HI ((B, A) :: LB) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o need S r SM g : Z) (x : PM.vstr) (bs : list Z).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S GB_SCR.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (PM.vs_cap x).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 (need - PM.vs_cap x).
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 (PM.vs_size x).
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 (PM.vs_size x).
Hypothesis A15 : getr R0 (reg 15) = Z_to_bv 64 0.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KC0 : NEM.kcontent RSEGS M0 o x bs.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis Hneed : PM.vs_cap x < need <= SM.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B A : Z) (cr' : credit),
  regs_preserved R0 R' -> A = PQAS.gcount (PM.vs_cap x) need ->
  L5.defined M' o 24 -> L5.u64_at RSEGS M' o (A + 1) -> L5.u64_at RSEGS M' (o + 16) B ->
  L5.defined M' B A -> L5.bytes_at RSEGS M' B bs -> 4096 <= B -> B + A <= hl_ceil L ->
  PQM.ks_ok SM (PM.VLong A need B) (g + 1) -> need < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
  L5C.hpres L LB S GB_SCR [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  model_but_vm model0 model' -> hi_heap HI ((B, A) :: LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let A : Z := PQAS.gcount (PM.vs_cap x) need.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))) /\ L5.u64_at RSEGS M (S - 64) (bv_unsigned (getr R0 (reg 22)))
  /\ L5.u64_at RSEGS M (S - 72) (bv_unsigned (getr R0 (reg 23))) /\ L5.u64_at RSEGS M (S - 80) (bv_unsigned (getr R0 (reg 24))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S GB_SCR [(o, 24)] M0 M /\ PMK.dk L LB S GB_SCR M0 M /\ L5C.stk (hl_sptop L) M S GB_SCR /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_352 ())). Qed.

Lemma x_cases' : (exists n0, x = PM.VShort n0) \/ (exists c n p, x = PM.VLong c n p).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_353 ())). Qed.
Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_354 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14272 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14272 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_355 ())). Qed.

(* [comment removed for export] *)
Lemma cap_ge : 22 <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_356 ())). Qed.
Lemma size_le_cap : 0 <= PM.vs_size x <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_357 ())). Qed.
Lemma growth : PQM.ks_ok SM (PM.VLong A need 0) (g + 1) /\ 2 * PQM.ks_alloc x <= A /\ 48 <= A /\ A <= 2 * SM + 8 /\ A mod 8 = 0
               /\ need < A /\ 26 <= A <= PQM.KCAP /\ A mod 2 = 0 /\ g < PQM.GMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_358 ())). Qed.
Lemma growth_B B : PQM.ks_ok SM (PM.VLong A need B) (g + 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_359 ())). Qed.
Lemma alloc_le : PQM.ks_alloc x <= SM.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_360 ())). Qed.
Lemma A_eq : A = 8 * (Z.max (2 * PM.vs_cap x) need / 8) + 8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_361 ())). Qed.

(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 80 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_362 ())). Qed.

Lemma mem_ok_callee M1 M3 LBc scr :
  mem_ok M1 -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> incl LB LBc -> PMFR.brange L LBc -> 0 <= scr -> 80 + scr <= GB_SCR ->
  L5C.stk (hl_sptop L) M1 (S - 80) scr -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_363 ())). Qed.

Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 80 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_364 ())). Qed.

Lemma saves_callee M1 M3 LBc scr :
  saves M1 -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> 0 <= scr -> L5C.stk (hl_sptop L) M1 (S - 80) scr -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_365 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_callee M1 M3 LBc scr :
  kstr_at M1 o x -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> incl (PM.vs_own x) LBc -> PMFR.brange L LBc -> 0 <= scr ->
  L5C.stk (hl_sptop L) M1 (S - 80) scr -> kstr_at M3 o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_366 ())). Qed.

Lemma stk_new M1 : mem_ok M1 -> L5C.stk (hl_sptop L) M1 (S - 80) PMSP.OPNEW_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_367 ())). Qed.

(* [comment removed for export] *)
Lemma KCF : L5.bytes_at RSEGS M0 (PM.vs_data o x) bs /\ NEM.bytes_ok bs /\ Z.of_nat (length bs) = PM.vs_size x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_368 ())). Qed.
Lemma bytes_frame M M1 : L5.bytes_at RSEGS M (PM.vs_data o x) bs -> kstr_at M o x -> hi_heap HI (PM.vs_own x ++ LB) cr0 M (m_vmmaps model0) ->
  (forall a, 0 <= a < 2 ^ 64 -> (S - 80 <= a < S) -> True) ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 80 <= i < S) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.bytes_at RSEGS M1 (PM.vs_data o x) bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_369 ())). Qed.
Lemma bytes_callee M1 M3 LBc scr :
  L5.bytes_at RSEGS M1 (PM.vs_data o x) bs -> kstr_at M1 o x -> L5C.hpres L LBc (S - 80) scr [] M1 M3 -> incl (PM.vs_own x) LBc -> PMFR.brange L LBc -> 0 <= scr ->
  L5C.stk (hl_sptop L) M1 (S - 80) scr -> L5.bytes_at RSEGS M3 (PM.vs_data o x) bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_370 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  L5.u64_at RSEGS M1 o (A + 1) -> L5.u64_at RSEGS M1 (o + 16) B -> L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L ->
  mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) -> model_but_vm model0 model1 ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x6643c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_371 ())). Qed.

(* [comment removed for export] *)
Lemma cs_fin (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S ->
  getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  getr R1 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 22))) -> getr R1 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 23))) ->
  getr R1 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 24))) ->
  (forall k, In k [3; 4; 25; 26; 27]%nat -> getr R1 (reg k) = getr R0 (reg k)) ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_372 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_F (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 23) = Z_to_bv 64 A -> getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66404 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_373 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_Ts (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (n0 B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VShort n0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 22 -> getr R1 (reg 19) = Z_to_bv 64 0 ->
  getr R1 (reg 20) = Z_to_bv 64 n0 -> getr R1 (reg 22) = Z_to_bv 64 n0 -> getr R1 (reg 23) = Z_to_bv 64 A -> getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663d0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_374 ())). Qed.

(* [comment removed for export] *)
Lemma tail_Td (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c n p B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> x = PM.VLong c n p ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (c - 1) -> getr R1 (reg 19) = Z_to_bv 64 0 ->
  getr R1 (reg 20) = Z_to_bv 64 n -> getr R1 (reg 21) = Z_to_bv 64 p -> getr R1 (reg 22) = Z_to_bv 64 n -> getr R1 (reg 23) = Z_to_bv 64 A ->
  getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L -> B <> p ->
  hi_heap HI ((B, A) :: (p, c) :: LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663d0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_375 ())). Qed.

(* [comment removed for export] *)
Lemma x_cases : (exists n0, x = PM.VShort n0) \/ (exists c n p, x = PM.VLong c n p).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_376 ())). Qed.

Lemma at_648 (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (PM.vs_cap x) -> getr R1 (reg 19) = Z_to_bv 64 0 ->
  getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 21) = Z_to_bv 64 (PM.vs_data o x) -> getr R1 (reg 22) = Z_to_bv 64 (PM.vs_size x) ->
  getr R1 (reg 23) = Z_to_bv 64 A -> getr R1 (reg 24) = Z_to_bv 64 B ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> 4096 <= B -> B + A <= hl_ceil L -> (forall c n p, x = PM.VLong c n p -> B <> p) ->
  hi_heap HI ((B, A) :: PM.vs_own x ++ LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663d0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_377 ())). Qed.

(* [comment removed for export] *)
Lemma after_new (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (B : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (PM.vs_cap x) -> getr R1 (reg 10) = Z_to_bv 64 B ->
  getr R1 (reg 19) = Z_to_bv 64 0 -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 21) = Z_to_bv 64 (PM.vs_data o x) ->
  getr R1 (reg 22) = Z_to_bv 64 (PM.vs_size x) -> getr R1 (reg 23) = Z_to_bv 64 A ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 (PM.vs_data o x) bs ->
  L5.defined M1 B A -> 4096 <= B -> B + A <= hl_ceil L -> (forall c n p, x = PM.VLong c n p -> B + A <= p \/ p + c <= B) ->
  hi_heap HI ((B, A) :: PM.vs_own x ++ LB) cr1 M1 (m_vmmaps model1) -> model_but_vm model0 model1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A need B) (g + 1)) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x663b8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_378 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma grow (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 80) -> getr R1 (reg 8) = Z_to_bv 64 o -> getr R1 (reg 9) = Z_to_bv 64 (PM.vs_cap x) ->
  getr R1 (reg 12) = Z_to_bv 64 (Z.max (2 * PM.vs_cap x) need) -> getr R1 (reg 19) = Z_to_bv 64 0 -> getr R1 (reg 20) = Z_to_bv 64 (PM.vs_size x) ->
  getr R1 (reg 21) = Z_to_bv 64 (PM.vs_data o x) -> getr R1 (reg 22) = Z_to_bv 64 (PM.vs_size x) ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 (PM.vs_data o x) bs ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x6638c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_379 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_S (n0 : Z) : x = PM.VShort n0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x662f8 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_380 ())). Qed.

(* [comment removed for export] *)
Lemma entry_L (c n p : Z) : x = PM.VLong c n p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x662f8 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_381 ())). Qed.

(* [comment removed for export] *)
Lemma gb_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x662f8 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_382 ())). Qed.

End Call.

Theorem gb_ok : PQASC.gb_specC RSEGS AD L HI 0x662f8.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSGbC ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_383 ())). Qed.

End WithHeap.
End PQADGBC.

End PnAdSGbC.
Module PnAdSIsTs2P.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.

Module PQADIST2P.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
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
Module Pad_isTs2 := BndP_Ns_033.LibSegNs_ad_isTs2.
Definition KS_ad_isTs2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_isTs2.regs0 Pad_isTs2.regs_out0).
Lemma KS_ad_isTs2_ok : BG.kept_ok 64 Pad_isTs2.regs0 Pad_isTs2.regs_out0 KS_ad_isTs2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ad_isTs2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) -> getr R (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 9))) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> 1 <= (V 36%nat) <= 22 -> 1 <= ((V 34%nat) + (V 36%nat)) <= 22 ->
  0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 1) -> ~ (((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) <= bv_unsigned a < ((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 0) <= i < ((bv_unsigned (getr R (reg 9))) + 0) + 1) -> ~ (((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) <= i < ((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3cee8 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_isTs2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 249632
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1) 0
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 9))) ((2 * (V 34%nat)) + (2 * (V 36%nat)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G18 G19 G20 G21 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 pvzI7 K9 pvzI8 pvzI9 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K8l; move K8l before pvzI7; pose proof (proj2 pvzI7) as K8r; move K8r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pad_isTs2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pad_isTs2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pad_isTs2.kn0).
  { unfold know_ok, Pad_isTs2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear) | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | byte_tac ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K11l K11r K13l K13r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K13l K13r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K11l K11r K13l K13r HV37l HV37r K12l K12r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pad_isTs2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pad_isTs2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 1) -> ~ (((((bv_unsigned (getr R (reg 9))) + 1) + (vz_34 + vz_36)) + 0) <= bv_unsigned a < ((((bv_unsigned (getr R (reg 9))) + 1) + (vz_34 + vz_36)) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pad_isTs2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K5 HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pad_isTs2.ps0) with 0xb9d7c in Hms. change (SR.ps_regs Pad_isTs2.ps0) with (map (fun i => (i, nth i Pad_isTs2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pad_isTs2.ps0) with Pad_isTs2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pad_isTs2.regs0 Pad_isTs2.regs_out0 64 KS_ad_isTs2 KS_ad_isTs2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pad_isTs2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pad_isTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_isTs2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pad_isTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_isTs2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pad_isTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_isTs2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pad_isTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_isTs2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pad_isTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | byte_tac ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PQADIST2P.

End PnAdSIsTs2P.
Module PnAdSInsC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSInsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3c73c_3c740 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3c898_3c89c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSIsTs2P.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSInsC () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC8src_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC3BRXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC3SBFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5src_qC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<bytes_at_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<bytes_ok_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC3KCFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib7Mh_00906L5Core3L5C<bytes_at_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K:ret_ok_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove5PMCPS@memmove_disjointC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove4PMCP:wbytes_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove4PMCP>wbytes_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<rdn_bytes_atC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7bv_wrapC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib5Lists7ListDef:Forall_indC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K=kept_ok_indexC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c898_3c89c7W_3cf14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c898_3c89c7F_3cf14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c898_3c89c7D_3cf14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5reg_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isRs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC7land2_0C1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6cs_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC;size_le_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isRsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isRl_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5sz_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isRlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC9src_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC;src_out_hdrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2Bapart_of_pointwiseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC<memmove_rdnCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC;saves_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6kc_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5ret_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subc69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC5ret_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188;PnAdSIsTs2P9PQADIST2P=ad_isTs2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188;PnAdSIsTs2P9PQADIST2P7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6move_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188;PnAdSIsTs2P9PQADIST2P;KS_ad_isTs2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP<ad_isTl_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6move_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP:KS_ad_isTlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_isG_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP9KS_ad_isGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6GB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6stk_gbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC8gb_specCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC8saves_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC9mem_ok_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6back_GC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC6GB_SCRC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib7Mh_0021ENs0_code_r3c73c_3c7407W_3cdb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c73c_3c7407F_3cdb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3c73c_3c7407D_3cdb8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_iwS_concC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C56Stdlib6ZArith6BinInt1Z7sub_0_rc69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC8ret_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6safe_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwS_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC7mem_ok0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;ad_iwL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC6safe_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsP8PQADINSP;KS_ad_iwL_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC7entry_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC7entry_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC7src_okCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC:src_okC_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSInsC8PQADINSC8ins_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC9ins_specCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADINSC.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation kcontent := (NEM.kcontent RSEGS).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) [] (Mh_0188_blobs1.kr_b_384 ())). Qed.

Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) [] (Mh_0188_blobs1.kr_b_385 ())). Qed.

Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) [] (Mh_0188_blobs1.kr_b_386 ())). Qed.

(* [comment removed for export] *)
Lemma cndS sz : 0 <= sz <= 22 -> (((18446744073709551615 * sz) mod 2 ^ 64) + 22) mod 2 ^ 64 = 22 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) [] (Mh_0188_blobs1.kr_b_387 ())). Qed.
Lemma cndL sz w : 0 <= sz < 2 * (w / 2) -> 0 <= w < 2 ^ 62 ->
  (((((18446744073709551615 * sz) mod 2 ^ 64) + ((2 * (w / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = 2 * (w / 2) - 1 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) [] (Mh_0188_blobs1.kr_b_388 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_at_agree (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> L5C.agree_on M M' o 24 -> (forall c n p, x = PM.VLong c n p -> L5.defined M' p c) ->
  kstr_at M o x -> kstr_at M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) [] (Mh_0188_blobs1.kr_b_389 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.
Let GB := PQADGBC.gb_ok L HI LY HIok OPN OPD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o q n S r SM g : Z) (x : PM.vstr) (bs sbs : list Z).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 q.
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 (q + n).
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n.
Hypothesis Hroom : PM.vs_size x + n <= SM.
Hypothesis SRC : PQAS.src_ok RSEGS L M0 LB S o q n.
Hypothesis SBS : Z.of_nat (length sbs) = n /\ L5.bytes_at RSEGS M0 q sbs /\ NEM.bytes_ok sbs.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KC0 : kcontent M0 o x bs.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> kcontent M' o x' (bs ++ sbs) -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
  L5C.hpres L LB S 14336 [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let sz : Z := PM.vs_size x.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_390 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_391 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14336 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14336 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_392 ())). Qed.

Lemma cap_ge : 22 <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_393 ())). Qed.
Lemma size_le_cap : 0 <= sz <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_394 ())). Qed.
Lemma sz_SM : 0 <= sz <= SM /\ SM <= 2 ^ 29.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_395 ())). Qed.

(* [comment removed for export] *)
Lemma src_q : 0 <= q /\ q + n < 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_396 ())). Qed.
Lemma src_kept i : 0 <= i < n -> L5C.kept L LB S 14336 [(o, 24)] (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_397 ())). Qed.
Lemma src_out_hdr i : 0 <= i < n -> ~ (o <= q + i < o + 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_398 ())). Qed.
Lemma src_client i : 0 <= i < n -> client_addr L LB S 14336 (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_399 ())). Qed.
(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_400 ())). Qed.

Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 64 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_401 ())). Qed.

(* [comment removed for export] *)
Lemma KCF : L5.bytes_at RSEGS M0 (PM.vs_data o x) bs /\ NEM.bytes_ok bs /\ Z.of_nat (length bs) = sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_402 ())). Qed.
Lemma SBF : Z.of_nat (length sbs) = n /\ L5.bytes_at RSEGS M0 q sbs /\ NEM.bytes_ok sbs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_403 ())). Qed.
Lemma src_bytes M : mem_ok M -> L5.bytes_at RSEGS M q sbs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_404 ())). Qed.
Lemma kc_app M d x' : PM.vs_data o x' = d -> PM.vs_size x' = sz + n ->
  L5.bytes_at RSEGS M d bs -> L5.bytes_at RSEGS M (d + sz) sbs -> kcontent M o x' (bs ++ sbs).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_405 ())). Qed.
(* [comment removed for export] *)
Lemma memmove_rdnC (fx : FPState) R M (dst src m ra : Z) (cs : list Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 m ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra ->
  1 <= m -> 0 <= dst -> dst + m < 2 ^ 63 -> 0 <= src -> src + m < 2 ^ 63 -> (dst + m <= src \/ src + m <= dst) ->
  L5.writable RSEGS M dst m -> L5.bytes_at RSEGS M src cs -> NEM.bytes_ok cs -> Z.of_nat (length cs) = m ->
  exists R3 M3, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xb9d7c) M (seg_rom RSEGS)) (@mkst fx R3 (Z_to_bv 64 ra) M3 (seg_rom RSEGS))
    /\ mem_grows M M3
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + m) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.defined M3 dst m /\ L5.bytes_at RSEGS M3 dst cs
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_406 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (x' : PM.vstr) (g' : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  kstr_at M1 o x' -> kcontent M1 o x' (bs ++ sbs) -> PQM.ks_ok SM x' g' -> PM.vs_size x' = sz + n -> mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') -> model_but_vm model0 model1 ->
  hi_heap HI (PM.vs_own x' ++ LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cf5c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_407 ())). Qed.

(* [comment removed for export] *)
Lemma cs_fin (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S ->
  getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R0 (reg k)) ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_408 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VShort (sz + n)) -> kcontent M1 o (PM.VShort (sz + n)) (bs ++ sbs) -> sz + n <= 22 ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cf20 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_409 ())). Qed.

(* [comment removed for export] *)
Lemma ret_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> kcontent M1 o (PM.VLong c' (sz + n) d) (bs ++ sbs) ->
  PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cf20 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_410 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma move_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 1) = Z_to_bv 64 0x3cf20 -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (o + 1 + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> L5.u8_at RSEGS M1 o (2 * (sz + n)) -> L5.bytes_at RSEGS M1 (o + 1) bs ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_411 ())). Qed.

(* [comment removed for export] *)
Lemma move_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 1) = Z_to_bv 64 0x3cf20 -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (d + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  L5.bytes_at RSEGS M1 d bs -> (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_412 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 (o + 1) ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 (o + 1) bs ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cee8 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_413 ())). Qed.

(* [comment removed for export] *)
Lemma tail_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 d ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (c' + 1) -> L5.u64_at RSEGS M1 (o + 16) d -> L5.defined M1 d c' -> L5.bytes_at RSEGS M1 d bs -> sz + n < c' -> 26 <= c' <= PQM.KCAP -> c' mod 2 = 0 ->
  PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' -> (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3cee8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_414 ())). Qed.

(* [comment removed for export] *)
Lemma back_G (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (A + 1) -> L5.u64_at RSEGS M1 (o + 16) B -> L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> sz + n < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
  PQM.ks_ok SM (PM.VLong A (sz + n) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (sz + n) B) (g + 1)) -> model_but_vm model0 model1 ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ceb0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_415 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_gb M2 M3 : saves M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_416 ())). Qed.
Lemma mem_ok_gb M2 M3 : mem_ok M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5.defined M3 o 24 -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_417 ())). Qed.
Lemma stk_gb M2 : mem_ok M2 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_418 ())). Qed.

(* [comment removed for export] *)
Lemma grow_call (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) :
  1 <= n -> PM.vs_cap x < sz + n ->
  getr R2 (reg 1) = Z_to_bv 64 0x3ceb0 -> getr R2 (reg 2) = Z_to_bv 64 (S - 64) -> getr R2 (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (reg 8) = Z_to_bv 64 sz -> getr R2 (reg 9) = Z_to_bv 64 o -> getr R2 (reg 10) = Z_to_bv 64 o -> getr R2 (reg 11) = Z_to_bv 64 (PM.vs_cap x) ->
  getr R2 (reg 12) = Z_to_bv 64 (sz + n - PM.vs_cap x) -> getr R2 (reg 13) = Z_to_bv 64 sz -> getr R2 (reg 14) = Z_to_bv 64 sz -> getr R2 (reg 15) = Z_to_bv 64 0 ->
  getr R2 (reg 18) = Z_to_bv 64 q -> getr R2 (reg 19) = Z_to_bv 64 (q + n) -> getr R2 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R2 -> saves M2 -> mem_ok M2 -> kstr_at M2 o x -> L5.bytes_at RSEGS M2 (PM.vs_data o x) bs ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M2 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x662f8 M2 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_419 ())). Qed.

(* [comment removed for export] *)
Lemma safe_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 (o + 1) bs -> hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ce2c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_420 ())). Qed.

(* [comment removed for export] *)
Lemma safe_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c sz0 p : Z) :
  x = PM.VLong c sz0 p -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 p bs -> hi_heap HI ((p, c) :: LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ce2c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_421 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_zero (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  n = 0 -> (forall k, In k (1%nat :: PMK.cs_all) -> getr R1 (reg k) = getr R0 (reg k)) -> mem_ok M1 -> kstr_at M1 o x ->
  L5.bytes_at RSEGS M1 (PM.vs_data o x) bs -> hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ce00 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_422 ())). Qed.

(* [comment removed for export] *)
Lemma entry_S (sz0 : Z) : x = PM.VShort sz0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3ccec M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_423 ())). Qed.

(* [comment removed for export] *)
Lemma entry_L (c sz0 p : Z) : x = PM.VLong c sz0 p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3ccec M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_424 ())). Qed.

(* [comment removed for export] *)
Lemma ins_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3ccec M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_425 ())). Qed.

End Call.

Theorem ins_ok : PQASC.ins_specC RSEGS AD L HI 0x3ccec.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSInsC ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_426 ())). Qed.




End WithHeap.
End PQADINSC.

End PnAdSInsC.
Module PnAdSJsTs2P.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.

Module PQADJST2P.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
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
Module Pad_jsTs2 := BndP_Ns_034.LibSegNs_ad_jsTs2.
Definition KS_ad_jsTs2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_jsTs2.regs0 Pad_jsTs2.regs_out0).
Lemma KS_ad_jsTs2_ok : BG.kept_ok 64 Pad_jsTs2.regs0 Pad_jsTs2.regs_out0 KS_ad_jsTs2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ad_jsTs2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 37%nat) + (V 36%nat)) -> getr R (reg 20) = Z_to_bv 64 ((V 34%nat) + (V 36%nat)) -> getr R (reg 21) = Z_to_bv 64 ((bv_unsigned (getr R (reg 9))) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (bv_unsigned (getr R (reg 9))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 9))) 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 9))) \/ (bv_unsigned (getr R (reg 9))) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (bv_unsigned (getr R (reg 9))) 24 -> L5.u8_at RSEGS M (bv_unsigned (getr R (reg 9))) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 -> 1 <= (V 36%nat) <= 22 -> 1 <= ((V 34%nat) + (V 36%nat)) <= 22 ->
  0 <= (V 37%nat) <= 140737488355328 -> 0 <= ((V 37%nat) + (V 36%nat)) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 1) -> ~ (((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) <= bv_unsigned a < ((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 9))) + 0) <= i < ((bv_unsigned (getr R (reg 9))) + 0) + 1) -> ~ (((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) <= i < ((((bv_unsigned (getr R (reg 9))) + 1) + ((V 34%nat) + (V 36%nat))) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3eb04 M) (st fx' R' 0xb9d7c M')
        /\ (forall x, In x KS_ad_jsTs2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 256828
        /\ getr R' (reg 10) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + (V 34%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1)
        /\ L5.u8_at RSEGS M' (((bv_unsigned (getr R (reg 9))) + ((V 34%nat) + (V 36%nat))) + 1) 0
        /\ L5.u8_at RSEGS M' (bv_unsigned (getr R (reg 9))) ((2 * (V 34%nat)) + (2 * (V 36%nat)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G18 G19 G20 G21 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 pvzI7 K9 pvzI8 pvzI9 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K8l; move K8l before pvzI7; pose proof (proj2 pvzI7) as K8r; move K8r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K11l; move K11l before pvzI9; pose proof (proj2 pvzI9) as K11r; move K11r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E Pad_jsTs2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pad_jsTs2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pad_jsTs2.kn0).
  { unfold know_ok, Pad_jsTs2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear) | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - K3l K3r K5) | evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | clear - K3l K3r K5; lia | clear - K3l K3r K5; lia | byte_tac ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K11l K11r K13l K13r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K13l K13r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K10l K10r K11l K11r K13l K13r HV37l HV37r K12l K12r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (Pad_jsTs2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change Pad_jsTs2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 9))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 9))) + 0) + 1) -> ~ (((((bv_unsigned (getr R (reg 9))) + 1) + (vz_34 + vz_36)) + 0) <= bv_unsigned a < ((((bv_unsigned (getr R (reg 9))) + 1) + (vz_34 + vz_36)) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pad_jsTs2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K5 HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pad_jsTs2.ps0) with 0xb9d7c in Hms. change (SR.ps_regs Pad_jsTs2.ps0) with (map (fun i => (i, nth i Pad_jsTs2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pad_jsTs2.ps0) with Pad_jsTs2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pad_jsTs2.regs0 Pad_jsTs2.regs_out0 64 KS_ad_jsTs2 KS_ad_jsTs2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pad_jsTs2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pad_jsTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_jsTs2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pad_jsTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_jsTs2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pad_jsTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_jsTs2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pad_jsTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pad_jsTs2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pad_jsTs2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5 HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | byte_tac ltac:(clear - HV34l HV34r K8l K8r K11l K11r HV36l HV36r K10l K10r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PQADJST2P.

End PnAdSJsTs2P.
Module PnAdSJnsC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import LeanFeed2.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJnsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3e358_3e35c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3e4b4_3e4b8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSGbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJsTs2P.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSJnsC () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC45stdpp;list_basics4list9app_inj_1C69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_mapC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib5Arith8PeanoNat3Nat3eqbK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic2or00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_mulC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7ek_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7dk_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C9stk_floorC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_capC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC8src_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6mem_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_piece_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8dk_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6frame0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC3BRXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC3SBFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5src_qC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<bytes_at_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC<bytes_ok_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC3KCFC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List:length_mapC46Stdlib9micromega;ZifyClasses7rew_iffC69OSSVerify5KrLib7Mh_00906L5Core3L5C<bytes_at_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K:ret_ok_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove5PMCPS@memmove_disjointC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove4PMCP:wbytes_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0142=PnSrcSMemmove4PMCP>wbytes_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<rdn_bytes_atC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7bv_wrapC47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib5Lists7ListDef:Forall_indC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K=kept_ok_indexC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K2CSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8hpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e4b4_3e4b87W_3eb30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e4b4_3e4b87F_3eb30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e4b4_3e4b87D_3eb30C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indc69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5kept0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5reg_uC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsRs_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC7land2_0C1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityC69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6cs_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8ks_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC3finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC;size_le_capC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsRsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsRl_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5sz_SMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsRlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC9src_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC;src_out_hdrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2Bapart_of_pointwiseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC<memmove_rdnCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC;saves_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC<mem_ok_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6kc_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5ret_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK>own_not_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8ek_pieceC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subc69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC=kstr_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC5ret_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188;PnAdSJsTs2P9PQADJST2P=ad_jsTs2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188;PnAdSJsTs2P9PQADJST2P7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6move_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0188;PnAdSJsTs2P9PQADJST2P;KS_ad_jsTs2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP<ad_jsTl_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_alloc_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6kl_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6move_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP:KS_ad_jsTlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jsG_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC:src_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6tail_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP9KS_ad_jsGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;ek_of_hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01887PnAdSGb6PQADGB6GB_SCRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK=ek_callee_in'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9stk_afterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6stk_gbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC8gb_specCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS6gcountC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC8saves_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC9mem_ok_gbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6back_GC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl15C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC6GB_SCRC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7W_3e9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7F_3e9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7D_3e9d4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;ad_jwS_concC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C56Stdlib6ZArith6BinInt1Z7sub_0_rc69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC8ret_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC6safe_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsP8PQADJNSP;KS_ad_jwS_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC7mem_ok0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC7entry_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC7entry_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC7src_okCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC:src_okC_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01889PnAdSJnsC8PQADJNSC8ins_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC9ins_specCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADJNSC.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation kcontent := (NEM.kcontent RSEGS).

Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) [] (Mh_0188_blobs1.kr_b_427 ())). Qed.

Lemma reg_u (R : bvmap 5 word) k v : getr R (reg k) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (getr R (reg k)) = v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) [] (Mh_0188_blobs1.kr_b_428 ())). Qed.

Lemma land2_0 n : 0 <= n <= 22 -> 0 <= Z.land ((2 * n) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) [] (Mh_0188_blobs1.kr_b_429 ())). Qed.

(* [comment removed for export] *)
Lemma cndS sz : 0 <= sz <= 22 -> (((18446744073709551615 * sz) mod 2 ^ 64) + 22) mod 2 ^ 64 = 22 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) [] (Mh_0188_blobs1.kr_b_430 ())). Qed.
Lemma cndL sz w : 0 <= sz < 2 * (w / 2) -> 0 <= w < 2 ^ 62 ->
  (((((18446744073709551615 * sz) mod 2 ^ 64) + ((2 * (w / 2)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64 = 2 * (w / 2) - 1 - sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) [] (Mh_0188_blobs1.kr_b_431 ())). Qed.

(* [comment removed for export] *)
Lemma kstr_at_agree (M M' : word -> option byte) o x :
  0 <= o -> o + 24 <= 2 ^ 64 -> L5C.agree_on M M' o 24 -> (forall c n p, x = PM.VLong c n p -> L5.defined M' p c) ->
  kstr_at M o x -> kstr_at M' o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) [] (Mh_0188_blobs1.kr_b_432 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.
Let GB := PQADGBC.gb_ok L HI LY HIok OPN OPD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LB : list (Z * Z)) (cr0 : credit).
Variables (o q n S r SM g : Z) (x : PM.vstr) (bs sbs : list Z).
Hypothesis HH0 : hi_heap HI (PM.vs_own x ++ LB) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 14336.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 o.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 (PM.vs_data o x + PM.vs_size x).
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 q.
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 (q + n).
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 n.
Hypothesis Hn : 0 <= n.
Hypothesis Hroom : PM.vs_size x + n <= SM.
Hypothesis SRC : PQAS.src_ok RSEGS L M0 LB S o q n.
Hypothesis SBS : Z.of_nat (length sbs) = n /\ L5.bytes_at RSEGS M0 q sbs /\ NEM.bytes_ok sbs.
Hypothesis KS0 : kstr_at M0 o x.
Hypothesis KC0 : kcontent M0 o x bs.
Hypothesis KO0 : PQM.ks_ok SM x g.
Hypothesis HSM : SM <= PQAS.SMMAX.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis CR0 : PMSP.credit_le (PQM.pot_ks L SM x g) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (x' : PM.vstr) (g' : Z) (cr' : credit),
  regs_preserved R0 R' -> kstr_at M' o x' -> kcontent M' o x' (bs ++ sbs) -> PQM.ks_ok SM x' g' -> PM.vs_size x' = PM.vs_size x + n ->
  L5C.hpres L LB S 14336 [(o, 24)] M0 M' ->
  PMSP.credit_keep cr0 cr' (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') ->
  model_but_vm model0 model' -> hi_heap HI (PM.vs_own x' ++ LB) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

Let sz : Z := PM.vs_size x.

(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))) /\ L5.u64_at RSEGS M (S - 48) (bv_unsigned (getr R0 (reg 20)))
  /\ L5.u64_at RSEGS M (S - 56) (bv_unsigned (getr R0 (reg 21))).
(* [comment removed for export] *)
Definition kept0 (R : bvmap 5 word) : Prop := forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg k) = getr R0 (reg k).
(* [comment removed for export] *)
Definition mem_ok (M : word -> option byte) : Prop :=
  PMK.ek L LB S 14336 [(o, 24)] M0 M /\ PMK.dk L LB S 14336 M0 M /\ L5C.stk (hl_sptop L) M S 14336 /\ L5.defined M o 24.

Lemma mem_ok0 : mem_ok M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_433 ())). Qed.

Lemma BRX : PMFR.brange L LB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_434 ())). Qed.

Lemma frame0 : 0x7fff7f800000 + 14336 <= S /\ S mod 16 = 0 /\ hl_ceil L + 14336 <= S /\ S <= hl_sptop L /\ hl_sptop L <= 2 ^ 47
               /\ 0x7fff80000000 <= hl_sptop L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_435 ())). Qed.

Lemma cap_ge : 22 <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_436 ())). Qed.
Lemma size_le_cap : 0 <= sz <= PM.vs_cap x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_437 ())). Qed.
Lemma sz_SM : 0 <= sz <= SM /\ SM <= 2 ^ 29.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_438 ())). Qed.

(* [comment removed for export] *)
Lemma src_q : 0 <= q /\ q + n < 2 ^ 47.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_439 ())). Qed.
Lemma src_kept i : 0 <= i < n -> L5C.kept L LB S 14336 [(o, 24)] (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_440 ())). Qed.
Lemma src_out_hdr i : 0 <= i < n -> ~ (o <= q + i < o + 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_441 ())). Qed.
Lemma src_client i : 0 <= i < n -> client_addr L LB S 14336 (q + i).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_442 ())). Qed.
(* [comment removed for export] *)
Lemma mem_ok_frame M M1 : mem_ok M -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 64 <= a < S) -> ~ (o <= a < o + 24) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> mem_ok M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_443 ())). Qed.

Lemma saves_frame M M1 : saves M -> (forall a, 0 <= a < 2 ^ 64 -> (S - 64 <= a < S) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> saves M1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_444 ())). Qed.

(* [comment removed for export] *)
Lemma KCF : L5.bytes_at RSEGS M0 (PM.vs_data o x) bs /\ NEM.bytes_ok bs /\ Z.of_nat (length bs) = sz.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_445 ())). Qed.
Lemma SBF : Z.of_nat (length sbs) = n /\ L5.bytes_at RSEGS M0 q sbs /\ NEM.bytes_ok sbs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_446 ())). Qed.
Lemma src_bytes M : mem_ok M -> L5.bytes_at RSEGS M q sbs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_447 ())). Qed.
Lemma kc_app M d x' : PM.vs_data o x' = d -> PM.vs_size x' = sz + n ->
  L5.bytes_at RSEGS M d bs -> L5.bytes_at RSEGS M (d + sz) sbs -> kcontent M o x' (bs ++ sbs).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_448 ())). Qed.
(* [comment removed for export] *)
Lemma memmove_rdnC (fx : FPState) R M (dst src m ra : Z) (cs : list Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 m ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra ->
  1 <= m -> 0 <= dst -> dst + m < 2 ^ 63 -> 0 <= src -> src + m < 2 ^ 63 -> (dst + m <= src \/ src + m <= dst) ->
  L5.writable RSEGS M dst m -> L5.bytes_at RSEGS M src cs -> NEM.bytes_ok cs -> Z.of_nat (length cs) = m ->
  exists R3 M3, msteps RSEGS (@mkst fx R (Z_to_bv 64 0xb9d7c) M (seg_rom RSEGS)) (@mkst fx R3 (Z_to_bv 64 ra) M3 (seg_rom RSEGS))
    /\ mem_grows M M3
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + m) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.defined M3 dst m /\ L5.bytes_at RSEGS M3 dst cs
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_449 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fin (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (x' : PM.vstr) (g' : Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  kstr_at M1 o x' -> kcontent M1 o x' (bs ++ sbs) -> PQM.ks_ok SM x' g' -> PM.vs_size x' = sz + n -> mem_ok M1 ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM x' g') -> model_but_vm model0 model1 ->
  hi_heap HI (PM.vs_own x' ++ LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb78 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_450 ())). Qed.

(* [comment removed for export] *)
Lemma cs_fin (R1 : bvmap 5 word) :
  getr R1 (reg 2) = Z_to_bv 64 S ->
  getr R1 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R1 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R1 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R1 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  getr R1 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 20))) -> getr R1 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 21))) ->
  (forall k, In k [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R0 (reg k)) ->
  forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_451 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VShort (sz + n)) -> kcontent M1 o (PM.VShort (sz + n)) (bs ++ sbs) -> sz + n <= 22 ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb3c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_452 ())). Qed.

(* [comment removed for export] *)
Lemma ret_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> kcontent M1 o (PM.VLong c' (sz + n) d) (bs ++ sbs) ->
  PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb3c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_453 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma move_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 1) = Z_to_bv 64 0x3eb3c -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (o + 1 + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> L5.u8_at RSEGS M1 o (2 * (sz + n)) -> L5.bytes_at RSEGS M1 (o + 1) bs ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_454 ())). Qed.

(* [comment removed for export] *)
Lemma move_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 1) = Z_to_bv 64 0x3eb3c -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 10) = Z_to_bv 64 (d + sz) -> getr R1 (reg 11) = Z_to_bv 64 q -> getr R1 (reg 12) = Z_to_bv 64 n ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o (PM.VLong c' (sz + n) d) -> PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' ->
  L5.bytes_at RSEGS M1 d bs -> (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb9d7c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_455 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tail_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n -> sz + n <= 22 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 (o + 1) ->
  kept0 R1 -> saves M1 -> mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 (o + 1) bs ->
  hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb04 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_456 ())). Qed.

(* [comment removed for export] *)
Lemma tail_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (c' d g' : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) -> getr R1 (reg 21) = Z_to_bv 64 d ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (c' + 1) -> L5.u64_at RSEGS M1 (o + 16) d -> L5.defined M1 d c' -> L5.bytes_at RSEGS M1 d bs -> sz + n < c' -> 26 <= c' <= PQM.KCAP -> c' mod 2 = 0 ->
  PQM.ks_ok SM (PM.VLong c' (sz + n) d) g' -> (forall i, 0 <= i < n -> ~ (d <= q + i < d + c')) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong c' (sz + n) d) g') -> model_but_vm model0 model1 ->
  hi_heap HI ((d, c') :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eb04 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_457 ())). Qed.

(* [comment removed for export] *)
Lemma back_G (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (A B : Z) (cr1 : credit) :
  PMSP.model_ok model1 -> 1 <= n ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 sz -> getr R1 (reg 9) = Z_to_bv 64 o ->
  getr R1 (reg 18) = Z_to_bv 64 q -> getr R1 (reg 19) = Z_to_bv 64 (q + n) -> getr R1 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R1 -> saves M1 -> mem_ok M1 ->
  L5.u64_at RSEGS M1 o (A + 1) -> L5.u64_at RSEGS M1 (o + 16) B -> L5.defined M1 B A -> L5.bytes_at RSEGS M1 B bs -> sz + n < A -> 26 <= A <= PQM.KCAP -> A mod 8 = 0 ->
  PQM.ks_ok SM (PM.VLong A (sz + n) B) (g + 1) ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_ks L SM x g) (PQM.pot_ks L SM (PM.VLong A (sz + n) B) (g + 1)) -> model_but_vm model0 model1 ->
  hi_heap HI ((B, A) :: LB) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3eacc M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_458 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma saves_gb M2 M3 : saves M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR -> saves M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_459 ())). Qed.
Lemma mem_ok_gb M2 M3 : mem_ok M2 -> L5C.hpres L LB (S - 64) PQADGB.GB_SCR [(o, 24)] M2 M3 -> L5.defined M3 o 24 -> mem_ok M3.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_460 ())). Qed.
Lemma stk_gb M2 : mem_ok M2 -> L5C.stk (hl_sptop L) M2 (S - 64) PQADGB.GB_SCR.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_461 ())). Qed.

(* [comment removed for export] *)
Lemma grow_call (fx2 : FPState) (R2 : bvmap 5 word) (M2 : word -> option byte) :
  1 <= n -> PM.vs_cap x < sz + n ->
  getr R2 (reg 1) = Z_to_bv 64 0x3eacc -> getr R2 (reg 2) = Z_to_bv 64 (S - 64) -> getr R2 (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R2 (reg 8) = Z_to_bv 64 sz -> getr R2 (reg 9) = Z_to_bv 64 o -> getr R2 (reg 10) = Z_to_bv 64 o -> getr R2 (reg 11) = Z_to_bv 64 (PM.vs_cap x) ->
  getr R2 (reg 12) = Z_to_bv 64 (sz + n - PM.vs_cap x) -> getr R2 (reg 13) = Z_to_bv 64 sz -> getr R2 (reg 14) = Z_to_bv 64 sz -> getr R2 (reg 15) = Z_to_bv 64 0 ->
  getr R2 (reg 18) = Z_to_bv 64 q -> getr R2 (reg 19) = Z_to_bv 64 (q + n) -> getr R2 (reg 20) = Z_to_bv 64 (sz + n) ->
  kept0 R2 -> saves M2 -> mem_ok M2 -> kstr_at M2 o x -> L5.bytes_at RSEGS M2 (PM.vs_data o x) bs ->
  hi_heap HI (PM.vs_own x ++ LB) cr0 M2 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x662f8 M2 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_462 ())). Qed.

(* [comment removed for export] *)
Lemma safe_S (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (sz0 : Z) :
  x = PM.VShort sz0 -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 (o + 1) bs -> hi_heap HI LB cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ea48 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_463 ())). Qed.

(* [comment removed for export] *)
Lemma safe_L (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (c sz0 p : Z) :
  x = PM.VLong c sz0 p -> 1 <= n ->
  getr R1 (reg 11) = Z_to_bv 64 n -> getr R1 (reg 12) = Z_to_bv 64 sz -> getr R1 (reg 13) = Z_to_bv 64 q -> getr R1 (reg 14) = Z_to_bv 64 (q + n) ->
  getr R1 (reg 1) = getr R0 (reg 1) -> getr R1 (reg 10) = Z_to_bv 64 o -> (forall k, In k PMK.cs_all -> getr R1 (reg k) = getr R0 (reg k)) ->
  mem_ok M1 -> kstr_at M1 o x -> L5.bytes_at RSEGS M1 p bs -> hi_heap HI ((p, c) :: LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ea48 M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_464 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ret_zero (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) :
  n = 0 -> (forall k, In k (1%nat :: PMK.cs_all) -> getr R1 (reg k) = getr R0 (reg k)) -> mem_ok M1 -> kstr_at M1 o x ->
  L5.bytes_at RSEGS M1 (PM.vs_data o x) bs -> hi_heap HI (PM.vs_own x ++ LB) cr0 M1 (m_vmmaps model0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ea1c M1 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_465 ())). Qed.

(* [comment removed for export] *)
Lemma entry_S (sz0 : Z) : x = PM.VShort sz0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3e908 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_466 ())). Qed.

(* [comment removed for export] *)
Lemma entry_L (c sz0 p : Z) : x = PM.VLong c sz0 p -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3e908 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0188 ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_467 ())). Qed.

(* [comment removed for export] *)
Lemma ins_main : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3e908 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"; "Call"] (Mh_0188_blobs1.kr_b_468 ())). Qed.

End Call.

Theorem ins_ok : PQASC.ins_specC RSEGS AD L HI 0x3e908.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSJnsC ()) ["WithHeap"] (Mh_0188_blobs1.kr_b_469 ())). Qed.




End WithHeap.
End PQADJNSC.

End PnAdSJnsC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef Utf8Facts.
Module PnAdVKitC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnMpKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnMpBaKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSIns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdLvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnSrcSMemmove OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSInsC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJnsC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef Utf8Facts.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac lia := L5FastLia.plia.

Module PNADVKC.
Import PMS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation AQ := PnLayoutQS.QADDR_S.
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation adaptor_at := (PQM.adaptor_at RSEGS AD PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).
Abbreviation kcontent := (NEM.kcontent RSEGS).

(* [comment removed for export] *)
Lemma ascii_utf8 l : NEM.ascii l -> utf8_valid l = true.
Proof.
  intros A.
  pose proof (UTF8F.valid_ascii_run l 0 (blen l) ltac:(lia) ltac:(unfold blen; lia) ltac:(lia)) as E.
  assert (Hb : forall j, 0 <= j < 0 + blen l -> 0 <= bat l j < 128).
  { intros j Hj. unfold bat, blen in *. unfold NEM.ascii in A. apply (Forall_nth (fun b => 0 <= b < 128) l); [exact A| lia]. }
  specialize (E Hb). rewrite Z.add_0_l in E. unfold blen in E. rewrite Nat2Z.id in E. change (Z.to_nat 0) with 0%nat in E.
  rewrite drop_0, drop_all in E. rewrite E. apply UTF8F.utf8_valid_nil.
Qed.
Lemma ascii_bytes_ok l : NEM.ascii l -> NEM.bytes_ok l.
Proof. exact (PQASC.ascii_bytes_ok l). Qed.
(* [comment removed for export] *)
Lemma utf8_valid_app_n (k : nat) : forall a b, (length a <= k)%nat -> utf8_valid a = true -> utf8_valid b = true -> utf8_valid (a ++ b) = true.
Proof.
  induction k as [|k IH]; intros a b Hk Ha Hb.
  - destruct a; [exact Hb| cbn in Hk; lia].
  - destruct a as [|c t]; [exact Hb|]. cbn [app]. rewrite UTF8F.utf8_valid_cons in Ha |- *. cbv zeta in Ha |- *.
    pose proof (UTF8F.utf8_trail_range c) as Tc.
    destruct (length (c :: t) <? Z.to_nat (utf8_trail c + 1))%nat eqn:E; [discriminate|]. apply Nat.ltb_ge in E.
    replace (length (c :: t ++ b) <? Z.to_nat (utf8_trail c + 1))%nat with false.
    2:{ symmetry. apply Nat.ltb_ge. change (c :: t ++ b) with ((c :: t) ++ b). rewrite length_app. lia. }
    apply andb_prop in Ha. destruct Ha as (L1 & V1).
    change (c :: t ++ b) with ((c :: t) ++ b). rewrite firstn_app, skipn_app.
    replace (Z.to_nat (utf8_trail c + 1) - length (c :: t))%nat with 0%nat by lia.
    change (firstn 0 b) with (@nil Z). change (skipn 0 b) with b. rewrite app_nil_r. rewrite L1. cbn [andb].
    apply IH; [| exact V1| exact Hb]. rewrite length_skipn. cbn [length] in *. lia.
Qed.
Lemma utf8_valid_app a b : utf8_valid a = true -> utf8_valid b = true -> utf8_valid (a ++ b) = true.
Proof. apply (utf8_valid_app_n (length a)). lia. Qed.
Lemma utf8_app_ascii a b : utf8_valid a = true -> NEM.ascii b -> utf8_valid (a ++ b) = true.
Proof. intros Ha Hb. apply utf8_valid_app; [exact Ha| apply ascii_utf8; exact Hb]. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Hypothesis OPN : PQAS.opnew_spec_n RSEGS AD L HI PQAS.NREQ.
Hypothesis OPD : PMS.opdel_spec L HI.
Let PBC := PQADPBC.pb_ok L HI LY HIok OPN OPD.
Let INSWC := PQADINSC.ins_ok L HI LY HIok OPN OPD.
Let INSCC := PQADJNSC.ins_ok L HI LY HIok OPN OPD.

Section Ctx.
Variables (M0 : word -> option byte) (K : TSet) (LBX : list (Z * Z)) (S oa ov osk oec : Z).
Hypothesis CX : PNADVK.ctx_ok L M0 K LBX S oa ov.
Local Ltac ctx := pose proof LY as LY'; pose proof HIok as HIok'; pose proof OPN as OPN'; pose proof OPD as OPD';
  pose proof CX as (K0 & STK0 & Ho1 & Ho2 & Ho3 & Hov1 & Hov2 & Hov3 & VIS0 & BASE0 & BRX).
#[local] Abbreviation cm := (PNADVK.cm L M0 LBX S oa ov osk oec).
#[local] Abbreviation world := (PNADVK.world ov).
Let frame0 := PNADVK.frame0 L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let IMG := PNADVK.IMG L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let ad_split := PNADVK.ad_split L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let pot_parts := PNADVK.pot_parts L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let after_strcall := PNADVK.after_strcall L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let heap_perm := PNADVK.heap_perm L HI HIok.
Let perm_key := PNADVK.perm_key L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let perm_kb := PNADVK.perm_kb L HI LY HIok OPN OPD M0 K LBX S oa ov CX.

(* [comment removed for export] *)
Lemma strcall_blocks (sp' wlo : Z) (M M' : word -> option byte) (LBs : list (Z * Z)) :
  S - 4096 <= sp' -> sp' <= S -> S <= wlo -> L5C.stk (hl_sptop L) M sp' WD.PB_SCR -> PMFR.brange L LBs ->
  L5C.hpres L LBs sp' WD.PB_SCR [(wlo, 24)] M M' ->
  (forall B m, In (B, m) LBs -> L5C.agree_on M M' B m) /\ (forall e, PQST.err_ok RSEGS AD AQ M e -> PQST.err_ok RSEGS AD AQ M' e).
Proof.
  ctx. intros Y1 Y2 Y3 STKc BRs HP. pose proof frame0 as (FL & A16 & SLO & SHI & STOP & STOP2). pose proof IMG as (I1 & I2).
  pose proof (PMK.ek_of_hpres L _ _ _ _ M M' HP) as EKc. assert (SC0 : 0 <= WD.PB_SCR) by (unfold WD.PB_SCR; lia).
  split.
  - intros B m Hin. apply (PMPK.ag_blk RSEGS L KL LBs sp' WD.PB_SCR [(wlo, 24)] M M' EKc STKc BRs B m Hin). intros i Hi Ii. apply PMFR.inW_inv1 in Ii.
    destruct (BRs B m Hin) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4. lia.
  - intros e. apply (PQKP.err_ok_keep RSEGS AD AQ L KL SF LBs sp' WD.PB_SCR [(wlo, 24)] M M' EKc);
      intros a Ha; apply PMFR.outside_of_not_inW; intros Ii; apply PMFR.inW_inv1 in Ii; cbn [pa_errcat_guard pa_atexit AD PnLayoutS.ADDR_S] in Ha; lia.
Qed.

(* [comment removed for export] *)
Lemma PBKEYC (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kbx : PM.vstr) (gx : Z) (cr : credit) (ra ch : Z) (bs : list Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 24) -> getr R (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 256 ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kbx gx) -> kcontent M (oa + 24) kx bs -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kx < PQM.SMK ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kx' : PM.vstr) (kgx' : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 24 \/ oa + 48 <= a) -> L5C.agree_on M M' a m) ->
      (forall B m, In (B, m) (PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX) -> L5C.agree_on M M' B m) -> (forall e, PQST.err_ok RSEGS AD AQ M e -> PQST.err_ok RSEGS AD AQ M' e) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx' kgx' kbx gx) -> kcontent M' (oa + 24) kx' (bs ++ [ch]) -> PQM.ks_ok PQM.SMK kx' kgx' -> PM.vs_size kx' = PM.vs_size kx + 1 ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx' kgx' kbx gx)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx' kgx' kbx gx) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x66444 M model) K.
Proof.
  ctx.
  intros Y1 Y2 Y3 X1 RA X2 X3 X4 X10 X11 Hch CM W AA KC KOK KOB ROOM CL MOK HH CONT.
  pose proof frame0 as (FL & A16 & SLO & SHI & STOP & STOP2). unfold PQM.ASIZE in Ho2, Hov3. pose proof IMG as (I1 & I2). pose proof CM as (EK & DK & STK).
  pose proof (ad_split M _ _ _ _ _ _ _ AA) as (HD & KY & KBm & LVm). pose proof LVm as (_ & _ & _ & HkX & _).
  set (LBk := PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX).
  pose proof (heap_perm _ _ cr M _ (perm_key lvX bX kX kx kgx kbx gx) HH) as HHp. fold LBk in HHp.
  assert (STKc : L5C.stk (hl_sptop L) M sp' WD.PB_SCR) by (unfold WD.PB_SCR; apply (PMK.stk_call L M S 28672 sp' 14336 STK); [lia|lia|lia| exact Y3]).
  pose proof (pot_parts lvX bX kX kx kgx kbx gx HkX KOK KOB) as (P1 & P2 & P3 & P4 & P5 & P6 & EP). rewrite EP in CL.
  assert (CRk : PMSP.credit_le (PQM.pot_ks L PQM.SMK kx kgx) cr).
  { apply (PQAS.cle_add_r _ _ cr P5 P6). apply (PQAS.cle_add_l _ _ cr P1 P2). unfold PM.credit_add in *. cbn [fst snd] in *. unfold PMSP.credit_le in *. cbn [fst snd] in *. lia. }
  assert (BRp : PMFR.brange L LBk) by (apply (PMFR.brange_of_heap L HI HIok _ LBk cr M _ HHp); apply incl_appr; apply incl_refl).
  pose proof (PBC : PQASC.pb_specC RSEGS AD L HI 0x66444) as PB'. unfold PQASC.pb_specC in PB'.
  apply (PB' fx R M model K LBk cr (oa + 24) ch sp' ra PQM.SMK kgx kx bs HHp MOK K0).
  { unfold WD.entry_scr. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hch. } { exact KY. } { exact KC. } { exact KOK. }
  { unfold PQAS.SMMAX, PQM.SMK. lia. } { exact ROOM. } { lia. } { lia. }
  { replace (oa + 24) with (oa + 8 * 3) by lia. apply PMPK.m8_add. exact Ho3. } { exact CRk. }
  intros fx' R' M' model' kx' kgx' cr' RP KY2 KC2 KO2 SZ2 HP CK2 MB2 HH2.
  destruct (after_strcall sp' (oa + 24) M M' LBk lvX bX kX kx kgx kbx gx kx' kgx' kbx gx cr (m_vmmaps model)
              ltac:(left; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact KY2]) Y1 Y2 STKc BRp HP CM W AA) as (CM' & W' & AGH & AA').
  destruct (strcall_blocks sp' (oa + 24) M M' LBk Y1 Y2 ltac:(lia) STKc BRp HP) as (BLK & ERRK).
  apply (CONT fx' R' M' model' kx' kgx' cr' RP CM' W' ltac:(intros a m Q1 Q2 Q3; apply AGH; lia) BLK ERRK AA' KC2 KO2 SZ2).
  - unfold PQM.pot_adaptor. cbn [PQM.a_lk PQM.a_key PQM.a_kg PQM.a_kb PQM.a_kbg]. apply PQAS.ck_add_l. apply PQAS.ck_add_r. exact CK2.
  - exact MB2.
  - apply (heap_perm _ _ cr' M' _ (Permutation_sym (perm_key lvX bX kX kx' kgx' kbx gx))). exact HH2.
Qed.

(* [comment removed for export] *)
Lemma PBCALLC (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kb1 : PM.vstr) (g1 : Z) (cr : credit) (ra ch : Z) (bs : list Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 48) -> getr R (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 256 ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kb1 g1) -> kcontent M (oa + 48) kb1 bs -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kb1 g1 -> PM.vs_size kb1 < PQM.SMB ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb1 g1) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kb2 : PM.vstr) (g2 : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 48 \/ oa + 72 <= a) -> L5C.agree_on M M' a m) ->
      (forall B m, In (B, m) (PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX) -> L5C.agree_on M M' B m) -> (forall e, PQST.err_ok RSEGS AD AQ M e -> PQST.err_ok RSEGS AD AQ M' e) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx kgx kb2 g2) -> kcontent M' (oa + 48) kb2 (bs ++ [ch]) -> PQM.ks_ok PQM.SMB kb2 g2 -> PM.vs_size kb2 = PM.vs_size kb1 + 1 ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb2 g2)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb2 g2) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x66444 M model) K.
Proof.
  ctx.
  intros Y1 Y2 Y3 X1 RA X2 X3 X4 X10 X11 Hch CM W AA KC KOK KO1 ROOM CL MOK HH CONT.
  pose proof frame0 as (FL & A16 & SLO & SHI & STOP & STOP2). unfold PQM.ASIZE in Ho2, Hov3. pose proof IMG as (I1 & I2). pose proof CM as (EK & DK & STK).
  pose proof (ad_split M _ _ _ _ _ _ _ AA) as (HD & KY & KBm & LVm). pose proof LVm as (_ & _ & _ & HkX & _).
  set (LBp := PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX).
  pose proof (heap_perm _ _ cr M _ (perm_kb lvX bX kX kx kgx kb1 g1) HH) as HHp. fold LBp in HHp.
  assert (STKc : L5C.stk (hl_sptop L) M sp' WD.PB_SCR) by (unfold WD.PB_SCR; apply (PMK.stk_call L M S 28672 sp' 14336 STK); [lia|lia|lia| exact Y3]).
  pose proof (pot_parts lvX bX kX kx kgx kb1 g1 HkX KOK KO1) as (P1 & P2 & P3 & P4 & P5 & P6 & EP). rewrite EP in CL.
  assert (CRk : PMSP.credit_le (PQM.pot_ks L PQM.SMB kb1 g1) cr) by (apply (PQAS.cle_add_l _ _ cr P3 P4); apply (PQAS.cle_add_l _ _ cr P1 P2); exact CL).
  assert (BRp : PMFR.brange L LBp) by (apply (PMFR.brange_of_heap L HI HIok _ LBp cr M _ HHp); apply incl_appr; apply incl_refl).
  pose proof (PBC : PQASC.pb_specC RSEGS AD L HI 0x66444) as PB'. unfold PQASC.pb_specC in PB'.
  apply (PB' fx R M model K LBp cr (oa + 48) ch sp' ra PQM.SMB g1 kb1 bs HHp MOK K0).
  { unfold WD.entry_scr. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { exact Hch. } { exact KBm. } { exact KC. } { exact KO1. }
  { unfold PQAS.SMMAX, PQM.SMB. lia. } { exact ROOM. } { lia. } { lia. }
  { replace (oa + 48) with (oa + 8 * 6) by lia. apply PMPK.m8_add. exact Ho3. } { exact CRk. }
  intros fx' R' M' model' kb2 g2 cr' RP KB2 KC2 KO2 SZ2 HP CK2 MB2 HH2.
  destruct (after_strcall sp' (oa + 48) M M' LBp lvX bX kX kx kgx kb1 g1 kx kgx kb2 g2 cr (m_vmmaps model)
              ltac:(right; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact KB2]) Y1 Y2 STKc BRp HP CM W AA) as (CM' & W' & AGH & AA').
  destruct (strcall_blocks sp' (oa + 48) M M' LBp Y1 Y2 ltac:(lia) STKc BRp HP) as (BLK & ERRK).
  apply (CONT fx' R' M' model' kb2 g2 cr' RP CM' W' ltac:(intros a m Q1 Q2 Q3; apply AGH; lia) BLK ERRK AA' KC2 KO2 SZ2).
  - unfold PQM.pot_adaptor. cbn [PQM.a_lk PQM.a_key PQM.a_kg PQM.a_kb PQM.a_kbg]. apply PQAS.ck_add_l. apply PQAS.ck_add_l. exact CK2.
  - exact MB2.
  - apply (heap_perm _ _ cr' M' _ (Permutation_sym (perm_kb lvX bX kX kx kgx kb2 g2))). exact HH2.
Qed.

(* [comment removed for export] *)
Lemma INSKBC (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kb1 : PM.vstr) (g1 : Z) (cr : credit) (ra : Z) (kcs bs : list Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 48) -> getr R (reg 11) = Z_to_bv 64 (PM.vs_data (oa + 48) kb1 + PM.vs_size kb1) ->
  getr R (reg 12) = Z_to_bv 64 (PM.vs_data (oa + 24) kx) -> getr R (reg 13) = Z_to_bv 64 (PM.vs_data (oa + 24) kx + PM.vs_size kx) -> getr R (reg 14) = Z_to_bv 64 (PM.vs_size kx) ->
  PM.vs_size kb1 + PM.vs_size kx <= PQM.SMB ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kb1 g1) -> kcontent M (oa + 24) kx kcs -> kcontent M (oa + 48) kb1 bs ->
  PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kb1 g1 ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb1 g1) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kb2 : PM.vstr) (g2 : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 48 \/ oa + 72 <= a) -> L5C.agree_on M M' a m) ->
      (forall B m, In (B, m) (PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX) -> L5C.agree_on M M' B m) -> (forall e, PQST.err_ok RSEGS AD AQ M e -> PQST.err_ok RSEGS AD AQ M' e) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx kgx kb2 g2) -> kcontent M' (oa + 48) kb2 (bs ++ kcs) -> PQM.ks_ok PQM.SMB kb2 g2 -> PM.vs_size kb2 = PM.vs_size kb1 + PM.vs_size kx ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb1 g1)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kb2 g2)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kb2 g2) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3ccec M model) K.
Proof.
  ctx.
  intros Y1 Y2 Y3 X1 RA X2 X3 X4 X10 X11 X12 X13 X14 ROOM CM W AA KCK KC KOK KO1 CL MOK HH CONT.
  pose proof frame0 as (FL & A16 & SLO & SHI & STOP & STOP2). unfold PQM.ASIZE in Ho2, Hov3. pose proof IMG as (I1 & I2). pose proof CM as (EK & DK & STK).
  pose proof (ad_split M _ _ _ _ _ _ _ AA) as (HD & KY & KBm & LVm). pose proof LVm as (_ & _ & _ & HkX & _).
  set (LBp := PQM.lvec_own bX kX ++ PM.vs_own kx ++ LBX).
  pose proof (heap_perm _ _ cr M _ (perm_kb lvX bX kX kx kgx kb1 g1) HH) as HHp. fold LBp in HHp.
  assert (STKc : L5C.stk (hl_sptop L) M sp' WD.PB_SCR) by (unfold WD.PB_SCR; apply (PMK.stk_call L M S 28672 sp' 14336 STK); [lia|lia|lia| exact Y3]).
  pose proof (pot_parts lvX bX kX kx kgx kb1 g1 HkX KOK KO1) as (P1 & P2 & P3 & P4 & P5 & P6 & EP). rewrite EP in CL.
  assert (CRk : PMSP.credit_le (PQM.pot_ks L PQM.SMB kb1 g1) cr) by (apply (PQAS.cle_add_l _ _ cr P3 P4); apply (PQAS.cle_add_l _ _ cr P1 P2); exact CL).
  assert (BRp : PMFR.brange L LBp) by (apply (PMFR.brange_of_heap L HI HIok _ LBp cr M _ HHp); apply incl_appr; apply incl_refl).
  pose proof KY as KYc. unfold PNADVK.KEY in KYc. destruct KYc as (DK24 & _ & KSH). pose proof KOK as (SZK & _ & _).
  pose proof KCK as ((BAk & BOKk) & LENk).
  assert (SRC : PQASC.src_okC RSEGS L M LBp sp' (oa + 48) (PM.vs_data (oa + 24) kx) (PM.vs_size kx) kcs).
  { split; [| split; [| split; [| split; [exact LENk| split; [exact BAk| exact BOKk]]]]]; destruct kx as [m|c m p]; cbn [PM.vs_data PM.vs_size] in *.
    - lia.
    - destruct KSH as (W0 & W8 & W16 & Hmc & Hc & He & DP & _).
      assert (Hin : In (p, c) LBp) by (unfold LBp; apply in_or_app; right; apply in_or_app; left; left; reflexivity). destruct (BRp p c Hin) as (Q0 & Q1 & Q4). lia.
    - destruct KSH as (Hm & _). lia.
    - destruct KSH as (W0 & W8 & W16 & Hmc & Hc & He & DP & _). unfold PQM.KCAP in Hc.
      assert (Hin : In (p, c) LBp) by (unfold LBp; apply in_or_app; right; apply in_or_app; left; left; reflexivity). destruct (BRp p c Hin) as (Q0 & Q1 & Q4). unfold hl_ceil in Q4. lia.
    - destruct KSH as (Hm & _). intros i Hi. apply (PMKP.kept_stack RSEGS L KL LBp M sp' WD.PB_SCR [(oa + 48, 24)] (oa + 24 + 1 + i) STKc); [unfold WD.PB_SCR; lia| lia|].
      apply PMFR.outside_of_not_inW. intros Ii. apply PMFR.inW_inv1 in Ii. lia.
    - destruct KSH as (W0 & W8 & W16 & Hmc & Hc & He & DP & _). unfold PQM.KCAP in Hc.
      assert (Hin : In (p, c) LBp) by (unfold LBp; apply in_or_app; right; apply in_or_app; left; left; reflexivity). destruct (BRp p c Hin) as (Q0 & Q1 & Q4).
      intros i Hi. apply (PMKP.kept_block RSEGS L KL LBp sp' WD.PB_SCR [(oa + 48, 24)] p c (p + i) Hin); [lia|lia|lia|lia|lia|].
      apply PMFR.outside_of_not_inW. intros Ii. apply PMFR.inW_inv1 in Ii. lia. }
  pose proof (INSWC : PQASC.ins_specC RSEGS AD L HI 0x3ccec) as INS'. unfold PQASC.ins_specC in INS'.
  apply (INS' fx R M model K LBp cr (oa + 48) (PM.vs_data (oa + 24) kx) (PM.vs_size kx) sp' ra PQM.SMB g1 kb1 bs kcs HHp MOK K0).
  { unfold WD.entry_scr. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { rewrite L5K.rl12. exact X12. } { rewrite L5K.rl13. exact X13. } { rewrite L5K.rl14. exact X14. }
  { lia. } { exact ROOM. } { exact SRC. } { exact KBm. } { exact KC. } { exact KO1. } { unfold PQAS.SMMAX, PQM.SMB. lia. } { lia. } { lia. }
  { replace (oa + 48) with (oa + 8 * 6) by lia. apply PMPK.m8_add. exact Ho3. } { exact CRk. }
  intros fx' R' M' model' kb2 g2 cr' RP KB2 KC2 KO2 SZ2 HP CK2 MB2 HH2.
  destruct (after_strcall sp' (oa + 48) M M' LBp lvX bX kX kx kgx kb1 g1 kx kgx kb2 g2 cr (m_vmmaps model)
              ltac:(right; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact KB2]) Y1 Y2 STKc BRp HP CM W AA) as (CM' & W' & AGH & AA').
  destruct (strcall_blocks sp' (oa + 48) M M' LBp Y1 Y2 ltac:(lia) STKc BRp HP) as (BLK & ERRK).
  apply (CONT fx' R' M' model' kb2 g2 cr' RP CM' W' ltac:(intros a m Q1 Q2 Q3; apply AGH; lia) BLK ERRK AA' KC2 KO2 SZ2).
  - unfold PQM.pot_adaptor. cbn [PQM.a_lk PQM.a_key PQM.a_kg PQM.a_kb PQM.a_kbg]. apply PQAS.ck_add_l. apply PQAS.ck_add_l. exact CK2.
  - exact MB2.
  - apply (heap_perm _ _ cr' M' _ (Permutation_sym (perm_kb lvX bX kX kx kgx kb2 g2))). exact HH2.
Qed.

(* [comment removed for export] *)
Lemma INSKEYC (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (lvX : list PQM.alvl) (bX kX : Z) (kx : PM.vstr) (kgx : Z)
      (kbx : PM.vstr) (gx : Z) (cr : credit) (ra q n : Z) (zs bs : list Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 24) -> getr R (reg 11) = Z_to_bv 64 (PM.vs_data (oa + 24) kx + PM.vs_size kx) ->
  getr R (reg 12) = Z_to_bv 64 q -> getr R (reg 13) = Z_to_bv 64 (q + n) -> getr R (reg 14) = Z_to_bv 64 n ->
  0 <= n -> PM.vs_size kx + n <= PQM.SMK -> 0x10000 <= q -> q + n <= 0xc6cc0 -> AX2.img_bytes RSEGS q (Z.to_nat n) = Some zs -> length zs = Z.to_nat n ->
  cm M -> world M -> adaptor_at M oa ov (PQM.AST lvX bX kX kx kgx kbx gx) -> kcontent M (oa + 24) kx bs -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx ->
  PMSP.credit_le (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx) ++ LBX) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kx' : PM.vstr) (kgx' : Z) (cr' : credit),
      regs_preserved R R' -> cm M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 24 \/ oa + 48 <= a) -> L5C.agree_on M M' a m) ->
      (forall B m, In (B, m) (PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX) -> L5C.agree_on M M' B m) -> (forall e, PQST.err_ok RSEGS AD AQ M e -> PQST.err_ok RSEGS AD AQ M' e) ->
      adaptor_at M' oa ov (PQM.AST lvX bX kX kx' kgx' kbx gx) -> kcontent M' (oa + 24) kx' (bs ++ zs) -> PQM.ks_ok PQM.SMK kx' kgx' -> PM.vs_size kx' = PM.vs_size kx + n ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx)) (PQM.pot_adaptor L (PQM.AST lvX bX kX kx' kgx' kbx gx)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (PQM.AST lvX bX kX kx' kgx' kbx gx) ++ LBX) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3e908 M model) K.
Proof.
  ctx.
  intros Y1 Y2 Y3 X1 RA X2 X3 X4 X10 X11 X12 X13 X14 Hn ROOM Hq1 Hq2 IMGB LEN CM W AA KC KOK KOB CL MOK HH CONT.
  pose proof frame0 as (FL & A16 & SLO & SHI & STOP & STOP2). unfold PQM.ASIZE in Ho2, Hov3. pose proof IMG as (I1 & I2). pose proof CM as (EK & DK & STK).
  pose proof (ad_split M _ _ _ _ _ _ _ AA) as (HD & KY & KBm & LVm). pose proof LVm as (_ & _ & _ & HkX & _).
  set (LBk := PQM.lvec_own bX kX ++ PM.vs_own kbx ++ LBX).
  pose proof (heap_perm _ _ cr M _ (perm_key lvX bX kX kx kgx kbx gx) HH) as HHp. fold LBk in HHp.
  assert (STKc : L5C.stk (hl_sptop L) M sp' WD.PB_SCR) by (unfold WD.PB_SCR; apply (PMK.stk_call L M S 28672 sp' 14336 STK); [lia|lia|lia| exact Y3]).
  pose proof (pot_parts lvX bX kX kx kgx kbx gx HkX KOK KOB) as (P1 & P2 & P3 & P4 & P5 & P6 & EP). rewrite EP in CL.
  assert (CRk : PMSP.credit_le (PQM.pot_ks L PQM.SMK kx kgx) cr).
  { apply (PQAS.cle_add_r _ _ cr P5 P6). apply (PQAS.cle_add_l _ _ cr P1 P2). unfold PM.credit_add in *. cbn [fst snd] in *. unfold PMSP.credit_le in *. cbn [fst snd] in *. lia. }
  assert (BRp : PMFR.brange L LBk) by (apply (PMFR.brange_of_heap L HI HIok _ LBk cr M _ HHp); apply incl_appr; apply incl_refl).
  destruct (AX2S.rdn_img RSEGS M (Z.to_nat n) (Z_to_bv 64 q) zs) as (ws & RD & MAP); [rewrite L5.unsigned_lit by lia; lia| | rewrite L5.unsigned_lit by lia; exact IMGB|].
  { intros j Hj. rewrite L5.unsigned_lit by lia. apply (PNADVK.world_img L HI LY HIok OPN OPD M0 K LBX S oa ov CX M W). lia. }
  assert (LB' : length ws = Z.to_nat n) by (rewrite <- LEN, <- MAP, length_map; reflexivity).
  pose proof (PQASC.bytes_at_of_rdn RSEGS M ws q ltac:(lia) ltac:(rewrite LB'; lia) ltac:(rewrite LB'; exact RD)) as (BAq & BOKq). rewrite MAP in BAq, BOKq.
  assert (SRC : PQASC.src_okC RSEGS L M LBk sp' (oa + 24) q n zs).
  { split; [lia|]. split; [lia|]. split.
    - intros i Hi. apply (PMKP.kept_cstatic RSEGS L KL LBk sp' WD.PB_SCR [(oa + 24, 24)] (q + i)); [apply (PMKS.cstatic_S L LY); lia|].
      apply PMFR.outside_of_not_inW. intros Ii. apply PMFR.inW_inv1 in Ii. lia.
    - split; [rewrite <- MAP, length_map; lia|]. split; [exact BAq| exact BOKq]. }
  pose proof (INSCC : PQASC.ins_specC RSEGS AD L HI 0x3e908) as INS'. unfold PQASC.ins_specC in INS'.
  apply (INS' fx R M model K LBk cr (oa + 24) q n sp' ra PQM.SMK kgx kx bs zs HHp MOK K0).
  { unfold WD.entry_scr. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact X1|]. split; [exact RA|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4| exact STKc]. }
  { rewrite L5K.rl10. exact X10. } { rewrite L5K.rl11. exact X11. } { rewrite L5K.rl12. exact X12. } { rewrite L5K.rl13. exact X13. } { rewrite L5K.rl14. exact X14. }
  { exact Hn. } { exact ROOM. } { exact SRC. } { exact KY. } { exact KC. } { exact KOK. } { unfold PQAS.SMMAX, PQM.SMK. lia. } { lia. } { lia. }
  { replace (oa + 24) with (oa + 8 * 3) by lia. apply PMPK.m8_add. exact Ho3. } { exact CRk. }
  intros fx' R' M' model' kx' kgx' cr' RP KY2 KC2 KO2 SZ2 HP CK2 MB2 HH2.
  destruct (after_strcall sp' (oa + 24) M M' LBk lvX bX kX kx kgx kbx gx kx' kgx' kbx gx cr (m_vmmaps model)
              ltac:(left; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact KY2]) Y1 Y2 STKc BRp HP CM W AA) as (CM' & W' & AGH & AA').
  destruct (strcall_blocks sp' (oa + 24) M M' LBk Y1 Y2 ltac:(lia) STKc BRp HP) as (BLK & ERRK).
  apply (CONT fx' R' M' model' kx' kgx' cr' RP CM' W' ltac:(intros a m Q1 Q2 Q3; apply AGH; lia) BLK ERRK AA' KC2 KO2 SZ2).
  - unfold PQM.pot_adaptor. cbn [PQM.a_lk PQM.a_key PQM.a_kg PQM.a_kb PQM.a_kbg]. apply PQAS.ck_add_l. apply PQAS.ck_add_r. exact CK2.
  - exact MB2.
  - apply (heap_perm _ _ cr' M' _ (Permutation_sym (perm_key lvX bX kX kx' kgx' kbx gx))). exact HH2.
Qed.

End Ctx.
End WithHeap.
End PNADVKC.

End PnAdVKitC.
