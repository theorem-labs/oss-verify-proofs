(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0206_blobs1.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module PnASrcReadP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnASrcReadP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrA0dC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0d3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrA0d_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrA0eC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP@defined_of_KUnkaC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0e3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrA0e_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrA0fC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrA0f3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrA0f_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrAgeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC4esubC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAge3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrAge_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrAltC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrAlt3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrAlt_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrBeqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBeq3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrBeq_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrBneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrBne3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrBne_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP8KS_asrC0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC06cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrC03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;KS_asrC0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrCgeC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrCge3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrCge_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrCltC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7PasrClt3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP<KS_asrClt_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7KS_asrDC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP5PasrD3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP:KS_asrD_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP8KS_asrE1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;KS_asrE1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP8KS_asrE2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE2<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP6PasrE23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;KS_asrE2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PMASRP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_004 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_005 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_006 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_007 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_008 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_009 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_010 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_011 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_012 ())). Qed.
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
Module PasrA0d := BndP_Na_009.LibSegNa_asrA0d.
Definition KS_asrA0d : list nat := Eval vm_compute in (BG.kept_list 80 PasrA0d.regs0 PasrA0d.regs_out0).
Lemma KS_asrA0d_ok : BG.kept_ok 80 PasrA0d.regs0 PasrA0d.regs_out0 KS_asrA0d = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_013 ())). Qed.
Lemma asrA0d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> 7036928 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 80) + 80 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1395208 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1394968 ->
  L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147625278 1 ->
  L5KA.zeros_at M 2147625259 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2ab0 M) (st fx' R' 0xf9c50 M')
        /\ (forall x, In x KS_asrA0d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863512
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 45%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 1023056
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 240)
        /\ getr R' (reg 21) = Z_to_bv 64 16384
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_014 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrA0e := BndP_Na_009.LibSegNa_asrA0e.
Definition KS_asrA0e : list nat := Eval vm_compute in (BG.kept_list 80 PasrA0e.regs0 PasrA0e.regs_out0).
Lemma KS_asrA0e_ok : BG.kept_ok 80 PasrA0e.regs0 PasrA0e.regs_out0 KS_asrA0e = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_015 ())). Qed.
Lemma asrA0e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 16384 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> 7036928 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 80) + 80 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1395208 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1394968 ->
  L5.u32_at RSEGS M ((V 45%nat) + 152) 2 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147625278 1 ->
  L5KA.zeros_at M 2147625259 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2ab0 M) (st fx' R' 0xd2dec M')
        /\ (forall x, In x KS_asrA0e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
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
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_016 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrA0f := BndP_Na_009.LibSegNa_asrA0f.
Definition KS_asrA0f : list nat := Eval vm_compute in (BG.kept_list 80 PasrA0f.regs0 PasrA0f.regs_out0).
Lemma KS_asrA0f_ok : BG.kept_ok 80 PasrA0f.regs0 PasrA0f.regs_out0 KS_asrA0f = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_017 ())). Qed.
Lemma asrA0f_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> 1 <= (V 38%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2ab0 M) (st fx' R' 0xd4b30 M')
        /\ (forall x, In x KS_asrA0f -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863208
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
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
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.defined M' ((V 36%nat) + 256) 8).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_018 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrAge := BndP_Na_009.LibSegNa_asrAge.
Definition KS_asrAge : list nat := Eval vm_compute in (BG.kept_list 80 PasrAge.regs0 PasrAge.regs_out0).
Lemma KS_asrAge_ok : BG.kept_ok 80 PasrAge.regs0 PasrAge.regs_out0 KS_asrAge = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_019 ())). Qed.
Lemma asrAge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) ->
  L5.defined M ((V 36%nat) + 256) 8 -> 1 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16384 -> 0 <= (((-1) * (V 33%nat)) + (V 38%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2ab0 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_asrAge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863040
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_020 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrAlt := BndP_Na_009.LibSegNa_asrAlt.
Definition KS_asrAlt : list nat := Eval vm_compute in (BG.kept_list 80 PasrAlt.regs0 PasrAlt.regs_out0).
Lemma KS_asrAlt_ok : BG.kept_ok 80 PasrAlt.regs0 PasrAlt.regs_out0 KS_asrAlt = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_021 ())). Qed.
Lemma asrAlt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) ->
  L5.defined M ((V 36%nat) + 256) 8 -> 2 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16383 -> 1 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2ab0 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_asrAlt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863040
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_022 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrBeq := BndP_Na_009.LibSegNa_asrBeq.
Definition KS_asrBeq : list nat := Eval vm_compute in (BG.kept_list 80 PasrBeq.regs0 PasrBeq.regs_out0).
Lemma KS_asrBeq_ok : BG.kept_ok 80 PasrBeq.regs0 PasrBeq.regs_out0 KS_asrBeq = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_023 ())). Qed.
Lemma asrBeq_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 21) = Z_to_bv 64 (V 39%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 1 <= (V 33%nat) <= 16384 ->
  1 <= (V 39%nat) <= 16384 -> 0 <= ((V 33%nat) - (V 39%nat)) <= 16383 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2b40 M) (st fx' R' 0xd2dec M')
        /\ (forall x, In x KS_asrBeq -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + (V 39%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_024 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrBne := BndP_Na_009.LibSegNa_asrBne.
Definition KS_asrBne : list nat := Eval vm_compute in (BG.kept_list 80 PasrBne.regs0 PasrBne.regs_out0).
Lemma KS_asrBne_ok : BG.kept_ok 80 PasrBne.regs0 PasrBne.regs_out0 KS_asrBne = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_025 ())). Qed.
Lemma asrBne_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 39%nat) ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 1 <= (V 39%nat) <= 16383 ->
  2 <= (V 38%nat) <= 16384 -> 1 <= ((V 38%nat) - (V 39%nat)) <= 16383 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2b40 M) (st fx' R' 0xd4b30 M')
        /\ (forall x, In x KS_asrBne -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863208
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 38%nat) - (V 39%nat))
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_026 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrC0 := BndP_Na_010.LibSegNa_asrC0.
Definition KS_asrC0 : list nat := Eval vm_compute in (BG.kept_list 80 PasrC0.regs0 PasrC0.regs_out0).
Lemma KS_asrC0_ok : BG.kept_ok 80 PasrC0.regs0 PasrC0.regs_out0 KS_asrC0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_027 ())). Qed.
Lemma asrC0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 0 <= (V 39%nat) <= 16383 ->
  1 <= (V 38%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2be8 M) (st fx' R' 0xd2dec M')
        /\ (forall x, In x KS_asrC0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_028 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrCge := BndP_Na_010.LibSegNa_asrCge.
Definition KS_asrCge : list nat := Eval vm_compute in (BG.kept_list 80 PasrCge.regs0 PasrCge.regs_out0).
Lemma KS_asrCge_ok : BG.kept_ok 80 PasrCge.regs0 PasrCge.regs_out0 KS_asrCge = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_029 ())). Qed.
Lemma asrCge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 1 <= (V 33%nat) <= 16383 ->
  1 <= (V 38%nat) <= 16383 -> 0 <= (((-1) * (V 33%nat)) + (V 38%nat)) <= 16383 -> 0 <= (V 39%nat) <= 16383 -> 0 <= (V 37%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2be8 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_asrCge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863256
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_030 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrClt := BndP_Na_010.LibSegNa_asrClt.
Definition KS_asrClt : list nat := Eval vm_compute in (BG.kept_list 80 PasrClt.regs0 PasrClt.regs_out0).
Lemma KS_asrClt_ok : BG.kept_ok 80 PasrClt.regs0 PasrClt.regs_out0 KS_asrClt = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_031 ())). Qed.
Lemma asrClt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 2 <= (V 33%nat) <= 16384 ->
  1 <= (V 38%nat) <= 16383 -> 1 <= ((V 33%nat) - (V 38%nat)) <= 16383 -> 0 <= (V 39%nat) <= 16383 -> 0 <= (V 37%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2be8 M) (st fx' R' 0x7ebbc M')
        /\ (forall x, In x KS_asrClt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 863256
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_032 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrD := BndP_Na_010.LibSegNa_asrD.
Definition KS_asrD : list nat := Eval vm_compute in (BG.kept_list 80 PasrD.regs0 PasrD.regs_out0).
Lemma KS_asrD_ok : BG.kept_ok 80 PasrD.regs0 PasrD.regs_out0 KS_asrD = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_033 ())). Qed.
Lemma asrD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 280) -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 1 <= (V 33%nat) <= 16384 ->
  1 <= (V 38%nat) <= 16383 -> 0 <= ((V 33%nat) - (V 38%nat)) <= 16383 -> 0 <= (V 39%nat) <= 16383 -> 4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2c18 M) (st fx' R' 0xd2dec M')
        /\ (forall x, In x KS_asrD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (V 39%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_034 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrE1 := BndP_Na_010.LibSegNa_asrE1.
Definition KS_asrE1 : list nat := Eval vm_compute in (BG.kept_list 80 PasrE1.regs0 PasrE1.regs_out0).
Lemma KS_asrE1_ok : BG.kept_ok 80 PasrE1.regs0 PasrE1.regs_out0 KS_asrE1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_035 ())). Qed.
Lemma asrE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 16384 -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 240) -> getr R (reg 21) = Z_to_bv 64 16384 -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> 7036928 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 80) + 80 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1395208 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1394968 ->
  L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147625278 1 ->
  L5KA.zeros_at M 2147625259 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2d18 M) (st fx' R' 0xd2dec M')
        /\ (forall x, In x KS_asrE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_036 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasrE2 := BndP_Na_010.LibSegNa_asrE2.
Definition KS_asrE2 : list nat := Eval vm_compute in (BG.kept_list 80 PasrE2.regs0 PasrE2.regs_out0).
Lemma KS_asrE2_ok : BG.kept_ok 80 PasrE2.regs0 PasrE2.regs_out0 KS_asrE2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_037 ())). Qed.
Lemma asrE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 19) = Z_to_bv 64 (V 37%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 240) -> getr R (reg 21) = Z_to_bv 64 16384 -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 7036928 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 ->
  L5.defined M ((V 36%nat) + 256) 8 -> 7036928 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 80) + 80 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1395208 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1394968 ->
  L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147625278 1 ->
  L5KA.zeros_at M 2147625259 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> 0 <= (V 33%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> ~ (((V 45%nat) + 152) <= bv_unsigned a < ((V 45%nat) + 152) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> ~ (((V 45%nat) + 152) <= i < ((V 45%nat) + 152) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xd2d18 M) (st fx' R' 0xd2dec M')
        /\ (forall x, In x KS_asrE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ L5.u32_at RSEGS M' ((V 45%nat) + 152) 2
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 64%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 65%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 66%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 67%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 68%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 69%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 70%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 72%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 73%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnASrcReadP ()) [] (Mh_0206_blobs1.kr_b_038 ())). Qed.
(* [comment removed for export] *)

End PMASRP.

End PnASrcReadP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool FunctionalExtensionality. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0206 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List9in_or_appC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6pm_scrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega7EnvRing5PExpr00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib5Arith8PeanoNat3Nat3eqbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C45stdpp9bitvector;definitions:bv_modulusC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_02136PgSrcA4PGSAAfill_buffer_specGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA;xsgetn_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_osC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_oisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA8owner_ok00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout;pa_src_readC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA4astkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5ffrsAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6W_srcGC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA6entryAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7ffroomBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA3ofrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA9read_argsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmParSpecs4PMPS6read_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS5ow_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8src_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmParSpecs4PMPS8read_resC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA6ahpresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA7dst_okGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA5aobjAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z7mod_addC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA6oo_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_vp_issC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_strbufC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout>pa_classic_impC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vstr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_iss_iosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8zeros_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PgSrcKitA5PGSKA9aobjA_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PgSrcKitA5PGSKA8src_visGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib7Mh_02139PgSrcKitA5PGSKA8iss_visGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8mach_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK7stk_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK;img_shz_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6frb_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK6brb_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK<fs_above_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_qcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sr_deC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6sr_remC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6ow_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4aaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_egC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM4sm_gC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4strm01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5sm_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK<iss_size_ltAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7src_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8lb_nodupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK=blk_obj_apartC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:app_rng_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213;PnASrcRead16PMASR1Bin_fframe_of_aobjAC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA6oo_winC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK<fst_neq_appAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK9blk_apartC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=app_rng_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213;PnASrcRead16PMASR1;in_block_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9wapp_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA4wappC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List9app_assocK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2ekC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR2dkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ahpres_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8agsh_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK:defined_dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8agsh_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PgSrcKitA5PGSKA?src_fields_updGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA6oo_updC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ>model_rt_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK8ret_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213;PnASrcRead16PMASR18cl_of_bfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR=aclient_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_pieceC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR4ek_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A;defined_visC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u64_at_visC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP:asrC0_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_02139PgSrcKitA5PGSKA>src_piece_issGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8ek_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8dk_transC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR:astk_growsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6apieceC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtc69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrCge_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_0213;PnASrcRead16PMASR16sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrClt_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A3cfgC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8astk_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9ek_calleeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR9dk_calleeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKAAastk_after_ahpresC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA5akeptC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR<stack_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7blk_outC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA9iss_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK9base_keepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9asrD_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213;PnASrcRead16PMASR1;defined_appC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8add_commC69OSSVerify5KrLib7Mh_0256;PnASrcReadK6PMASRK;memcpy_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8mod16_8'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA;stksh_keepAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA?shadow_zero_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ff_capC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ff_rsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PmParSpecs4PMPS8fill_resC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6unreadC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrBeq_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflc69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrBne_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrA0d_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASKAiss_unread_whereAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA7ffroomAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP:asrE1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP:asrE2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA7agA_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnASrcKit5PMASK;iss_st_updAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrA0e_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrA0f_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrAge_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP;asrAlt_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA>src_read_specGC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega6VarMap4findK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K45stdpp9bitvector;definitions2bv01K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t02C46Stdlib9micromega:ZMicromega=Zeval_formulaC46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00907PmModel2PM9nullis_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM=src_fields_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6iss_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0092:PmStaticsA5PMSTA8base_okAC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_02136PgSrcA4PGSA6oo_srcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7iosb_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR6cs_allC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM5CHUNKC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP8KS_asrC0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP7KS_asrDC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrBeqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrA0dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnStepA4PMKA8wapp_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP8KS_asrE1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP8KS_asrE2C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C69OSSVerify5KrLib7Mh_02137PnRunBA4PNRA3FCBC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00905PgSrc3PGS5owner00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM5srcst00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4strm00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR3r11C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR3r12C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib7Mh_0012ENa0_code_raf314_af3187W_d2d9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_raf314_af3187F_d2d9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_raf314_af3187D_d2d9cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrCgeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrCltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrBneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrA0eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrA0fC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrAgeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnASrcReadP6PMASRP9KS_asrAltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List9nth_errorC47Corelib4Init5Logic8eq_transK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallc69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC47Corelib4Init3Nat3addC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<eq_decidableC35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC0<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1>u8_of_KWord1maC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz05C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC09regs_out0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC06cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP18KS_atzC0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1;KS_atzC0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm9regs_out0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP18KS_atzCmC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1;KS_atzCm_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9ec_atexitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9asc_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ5ec_f1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ5ec_a1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<atexit_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9astack_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8aly_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA5ly_tpC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP7alignedC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<aior_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<asan_staticsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A=statics_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asc_got_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asc_got_hiC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsDiff_impl_subrelationC69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9aly_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA<ly_cxa_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9u8_at_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5ACimg_clear_mrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A<writable_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA<writable_imgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP9acxA_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA5ly_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST>in_foot_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA9ly_staticC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PnStepA25PMKA29rt_ro_bssC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA8u64_normC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA:cells_snocC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA>ctr_not_clientC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA@store_ok_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA:apiece_ctrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP:acxA3_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_Somec69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP:acxA5_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ5ec_f0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ5ec_a0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ6ec_atcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ5ec_nlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ:ec_cxa_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9ec_cxa_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ?cxa_atexit_specC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA7ret_rokC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00929PnStatics4PNST8dep_of_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_lec69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP7KS_acxAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_r6cfa8_6cfac7W_74970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_r6cfa8_6cfac7F_74970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0012ENa0_code_r6cfa8_6cfac7D_74970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA7NADDR_AC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP8KS_acxA3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP8KS_acxA5C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA3EXTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A@AS0_ALY_CELLS_D4C1?~~~~~~~~~~~~~~~".
Module Na0PgSrcRead.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmParSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0088.PmParStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnASrcReadK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnASrcRead1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnASrcReadP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_raf314_af318 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PgSrcKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunBA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis32 OAV := lazymatch goal with |- L5.u32_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u32_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Theorem src_read_okG : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PMA.xsgetn_spec L ar HI -> PGSA.src_read_specG RSEGS PMA.AD L ar HI PNRA.FCB.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0206 ()) ["WithHeap"] (Mh_0206_blobs1.kr_b_039 ())). Qed.

End WithHeap.
End PGSRDA.

End Na0PgSrcRead.
Module PnACValRP3.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnACValRP3 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3;KS_avrF5Z_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3;KS_avrF5Z_1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z3ps1C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z3kn0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop04I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3>KS_avrF5Z_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF5Z6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3>KS_avrF5Z_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P1_1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P13ps1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P2_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P29regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P2_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P2<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P23ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P23ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P2_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P26cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P2_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P4_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P49regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P4_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P43ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P43ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P43kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P4_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P46cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P4_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P5_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P59regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P5_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P53ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P53ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P53kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P5_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P56cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P5_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P6_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P69regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P6_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P63ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P63ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P63kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P6_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P66cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P6_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P7_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P79regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF5P7_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P73ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P73ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P73kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P7_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF5P76cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF5P7_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3;KS_avrF6Z_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3;KS_avrF6Z_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3>KS_avrF6Z_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF6Z6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3>KS_avrF6Z_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P2_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P29regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P2_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P23ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P23ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P2_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P26cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P2_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P4_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P49regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P4_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P43ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P43ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P43kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P4_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P46cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P4_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P5_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P59regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P5_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P53ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P53ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P53kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P5_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P56cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P5_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P6_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P69regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P6_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P63ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P63ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P63kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P6_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P66cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P6_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P7_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P79regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF6P7_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P73ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P73ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P73kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P7_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF6P76cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF6P7_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3;KS_avrF7Z_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3;KS_avrF7Z_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3>KS_avrF7Z_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP37PavrF7Z6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3>KS_avrF7Z_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P2_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P29regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P2_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P23ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P23ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P2_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P26cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P2_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P4_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P49regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P4_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P43ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P43ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P43kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P4_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P46cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P4_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P5_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P59regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P5_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P53ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P53ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P53kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P5_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P56cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P5_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P6_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P69regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P6_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P63ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P63ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P63kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P6_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P66cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P6_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P7_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P79regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3<KS_avrF7P7_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P73ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P73ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P73kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P7_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP38PavrF7P76cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP3:PECVALARP3?KS_avrF7P7_1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PECVALARP3.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_040 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_041 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_042 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_043 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_044 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_045 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_046 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_047 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_048 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_049 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_050 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_051 ())). Qed.
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
Module PavrF5Z := BndP_Na_028.LibSegNa_avrF5Z.
Definition KS_avrF5Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5Z.regs0 PavrF5Z.regs_out0).
Lemma KS_avrF5Z_0_ok : BG.kept_ok 60 PavrF5Z.regs0 PavrF5Z.regs_out0 KS_avrF5Z_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_052 ())). Qed.
Definition KS_avrF5Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5Z.regs0 PavrF5Z.regs_out1).
Lemma KS_avrF5Z_1_ok : BG.kept_ok 60 PavrF5Z.regs0 PavrF5Z.regs_out1 KS_avrF5Z_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_053 ())). Qed.
Lemma avrF5Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 5) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_054 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P1 := BndP_Na_028.LibSegNa_avrF5P1.
Definition KS_avrF5P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P1.regs0 PavrF5P1.regs_out0).
Lemma KS_avrF5P1_0_ok : BG.kept_ok 60 PavrF5P1.regs0 PavrF5P1.regs_out0 KS_avrF5P1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_055 ())). Qed.
Definition KS_avrF5P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P1.regs0 PavrF5P1.regs_out1).
Lemma KS_avrF5P1_1_ok : BG.kept_ok 60 PavrF5P1.regs0 PavrF5P1.regs_out1 KS_avrF5P1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_056 ())). Qed.
Lemma avrF5P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_057 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P2 := BndP_Na_028.LibSegNa_avrF5P2.
Definition KS_avrF5P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P2.regs0 PavrF5P2.regs_out0).
Lemma KS_avrF5P2_0_ok : BG.kept_ok 60 PavrF5P2.regs0 PavrF5P2.regs_out0 KS_avrF5P2_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_058 ())). Qed.
Definition KS_avrF5P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P2.regs0 PavrF5P2.regs_out1).
Lemma KS_avrF5P2_1_ok : BG.kept_ok 60 PavrF5P2.regs0 PavrF5P2.regs_out1 KS_avrF5P2_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_059 ())). Qed.
Lemma avrF5P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_060 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P3 := BndP_Na_028.LibSegNa_avrF5P3.
Definition KS_avrF5P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P3.regs0 PavrF5P3.regs_out0).
Lemma KS_avrF5P3_0_ok : BG.kept_ok 60 PavrF5P3.regs0 PavrF5P3.regs_out0 KS_avrF5P3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_061 ())). Qed.
Definition KS_avrF5P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P3.regs0 PavrF5P3.regs_out1).
Lemma KS_avrF5P3_1_ok : BG.kept_ok 60 PavrF5P3.regs0 PavrF5P3.regs_out1 KS_avrF5P3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_062 ())). Qed.
Lemma avrF5P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_063 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P4 := BndP_Na_028.LibSegNa_avrF5P4.
Definition KS_avrF5P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P4.regs0 PavrF5P4.regs_out0).
Lemma KS_avrF5P4_0_ok : BG.kept_ok 60 PavrF5P4.regs0 PavrF5P4.regs_out0 KS_avrF5P4_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_064 ())). Qed.
Definition KS_avrF5P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P4.regs0 PavrF5P4.regs_out1).
Lemma KS_avrF5P4_1_ok : BG.kept_ok 60 PavrF5P4.regs0 PavrF5P4.regs_out1 KS_avrF5P4_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_065 ())). Qed.
Lemma avrF5P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_066 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P5 := BndP_Na_028.LibSegNa_avrF5P5.
Definition KS_avrF5P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P5.regs0 PavrF5P5.regs_out0).
Lemma KS_avrF5P5_0_ok : BG.kept_ok 60 PavrF5P5.regs0 PavrF5P5.regs_out0 KS_avrF5P5_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_067 ())). Qed.
Definition KS_avrF5P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P5.regs0 PavrF5P5.regs_out1).
Lemma KS_avrF5P5_1_ok : BG.kept_ok 60 PavrF5P5.regs0 PavrF5P5.regs_out1 KS_avrF5P5_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_068 ())). Qed.
Lemma avrF5P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_069 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P6 := BndP_Na_028.LibSegNa_avrF5P6.
Definition KS_avrF5P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P6.regs0 PavrF5P6.regs_out0).
Lemma KS_avrF5P6_0_ok : BG.kept_ok 60 PavrF5P6.regs0 PavrF5P6.regs_out0 KS_avrF5P6_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_070 ())). Qed.
Definition KS_avrF5P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P6.regs0 PavrF5P6.regs_out1).
Lemma KS_avrF5P6_1_ok : BG.kept_ok 60 PavrF5P6.regs0 PavrF5P6.regs_out1 KS_avrF5P6_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_071 ())). Qed.
Lemma avrF5P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_072 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF5P7 := BndP_Na_028.LibSegNa_avrF5P7.
Definition KS_avrF5P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P7.regs0 PavrF5P7.regs_out0).
Lemma KS_avrF5P7_0_ok : BG.kept_ok 60 PavrF5P7.regs0 PavrF5P7.regs_out0 KS_avrF5P7_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_073 ())). Qed.
Definition KS_avrF5P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF5P7.regs0 PavrF5P7.regs_out1).
Lemma KS_avrF5P7_1_ok : BG.kept_ok 60 PavrF5P7.regs0 PavrF5P7.regs_out1 KS_avrF5P7_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_074 ())). Qed.
Lemma avrF5P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 5) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 5) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF5P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd367c M) (st fx' R' 0xd3698 M')
        /\ (forall x, In x KS_avrF5P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 5)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 5) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_075 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6Z := BndP_Na_029.LibSegNa_avrF6Z.
Definition KS_avrF6Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6Z.regs0 PavrF6Z.regs_out0).
Lemma KS_avrF6Z_0_ok : BG.kept_ok 60 PavrF6Z.regs0 PavrF6Z.regs_out0 KS_avrF6Z_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_076 ())). Qed.
Definition KS_avrF6Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6Z.regs0 PavrF6Z.regs_out1).
Lemma KS_avrF6Z_1_ok : BG.kept_ok 60 PavrF6Z.regs0 PavrF6Z.regs_out1 KS_avrF6Z_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_077 ())). Qed.
Lemma avrF6Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 6) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_078 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P1 := BndP_Na_028.LibSegNa_avrF6P1.
Definition KS_avrF6P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P1.regs0 PavrF6P1.regs_out0).
Lemma KS_avrF6P1_0_ok : BG.kept_ok 60 PavrF6P1.regs0 PavrF6P1.regs_out0 KS_avrF6P1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_079 ())). Qed.
Definition KS_avrF6P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P1.regs0 PavrF6P1.regs_out1).
Lemma KS_avrF6P1_1_ok : BG.kept_ok 60 PavrF6P1.regs0 PavrF6P1.regs_out1 KS_avrF6P1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_080 ())). Qed.
Lemma avrF6P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_081 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P2 := BndP_Na_028.LibSegNa_avrF6P2.
Definition KS_avrF6P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P2.regs0 PavrF6P2.regs_out0).
Lemma KS_avrF6P2_0_ok : BG.kept_ok 60 PavrF6P2.regs0 PavrF6P2.regs_out0 KS_avrF6P2_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_082 ())). Qed.
Definition KS_avrF6P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P2.regs0 PavrF6P2.regs_out1).
Lemma KS_avrF6P2_1_ok : BG.kept_ok 60 PavrF6P2.regs0 PavrF6P2.regs_out1 KS_avrF6P2_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_083 ())). Qed.
Lemma avrF6P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_084 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P3 := BndP_Na_028.LibSegNa_avrF6P3.
Definition KS_avrF6P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P3.regs0 PavrF6P3.regs_out0).
Lemma KS_avrF6P3_0_ok : BG.kept_ok 60 PavrF6P3.regs0 PavrF6P3.regs_out0 KS_avrF6P3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_085 ())). Qed.
Definition KS_avrF6P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P3.regs0 PavrF6P3.regs_out1).
Lemma KS_avrF6P3_1_ok : BG.kept_ok 60 PavrF6P3.regs0 PavrF6P3.regs_out1 KS_avrF6P3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_086 ())). Qed.
Lemma avrF6P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_087 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P4 := BndP_Na_029.LibSegNa_avrF6P4.
Definition KS_avrF6P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P4.regs0 PavrF6P4.regs_out0).
Lemma KS_avrF6P4_0_ok : BG.kept_ok 60 PavrF6P4.regs0 PavrF6P4.regs_out0 KS_avrF6P4_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_088 ())). Qed.
Definition KS_avrF6P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P4.regs0 PavrF6P4.regs_out1).
Lemma KS_avrF6P4_1_ok : BG.kept_ok 60 PavrF6P4.regs0 PavrF6P4.regs_out1 KS_avrF6P4_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_089 ())). Qed.
Lemma avrF6P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_090 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P5 := BndP_Na_029.LibSegNa_avrF6P5.
Definition KS_avrF6P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P5.regs0 PavrF6P5.regs_out0).
Lemma KS_avrF6P5_0_ok : BG.kept_ok 60 PavrF6P5.regs0 PavrF6P5.regs_out0 KS_avrF6P5_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_091 ())). Qed.
Definition KS_avrF6P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P5.regs0 PavrF6P5.regs_out1).
Lemma KS_avrF6P5_1_ok : BG.kept_ok 60 PavrF6P5.regs0 PavrF6P5.regs_out1 KS_avrF6P5_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_092 ())). Qed.
Lemma avrF6P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_093 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P6 := BndP_Na_029.LibSegNa_avrF6P6.
Definition KS_avrF6P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P6.regs0 PavrF6P6.regs_out0).
Lemma KS_avrF6P6_0_ok : BG.kept_ok 60 PavrF6P6.regs0 PavrF6P6.regs_out0 KS_avrF6P6_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_094 ())). Qed.
Definition KS_avrF6P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P6.regs0 PavrF6P6.regs_out1).
Lemma KS_avrF6P6_1_ok : BG.kept_ok 60 PavrF6P6.regs0 PavrF6P6.regs_out1 KS_avrF6P6_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_095 ())). Qed.
Lemma avrF6P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_096 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF6P7 := BndP_Na_029.LibSegNa_avrF6P7.
Definition KS_avrF6P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P7.regs0 PavrF6P7.regs_out0).
Lemma KS_avrF6P7_0_ok : BG.kept_ok 60 PavrF6P7.regs0 PavrF6P7.regs_out0 KS_avrF6P7_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_097 ())). Qed.
Definition KS_avrF6P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF6P7.regs0 PavrF6P7.regs_out1).
Lemma KS_avrF6P7_1_ok : BG.kept_ok 60 PavrF6P7.regs0 PavrF6P7.regs_out1 KS_avrF6P7_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_098 ())). Qed.
Lemma avrF6P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 6) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 6) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF6P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3698 M) (st fx' R' 0xd36b4 M')
        /\ (forall x, In x KS_avrF6P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 6)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 6) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_099 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7Z := BndP_Na_029.LibSegNa_avrF7Z.
Definition KS_avrF7Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7Z.regs0 PavrF7Z.regs_out0).
Lemma KS_avrF7Z_0_ok : BG.kept_ok 60 PavrF7Z.regs0 PavrF7Z.regs_out0 KS_avrF7Z_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_100 ())). Qed.
Definition KS_avrF7Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7Z.regs0 PavrF7Z.regs_out1).
Lemma KS_avrF7Z_1_ok : BG.kept_ok 60 PavrF7Z.regs0 PavrF7Z.regs_out1 KS_avrF7Z_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_101 ())). Qed.
Lemma avrF7Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 7) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_102 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P1 := BndP_Na_029.LibSegNa_avrF7P1.
Definition KS_avrF7P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P1.regs0 PavrF7P1.regs_out0).
Lemma KS_avrF7P1_0_ok : BG.kept_ok 60 PavrF7P1.regs0 PavrF7P1.regs_out0 KS_avrF7P1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_103 ())). Qed.
Definition KS_avrF7P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P1.regs0 PavrF7P1.regs_out1).
Lemma KS_avrF7P1_1_ok : BG.kept_ok 60 PavrF7P1.regs0 PavrF7P1.regs_out1 KS_avrF7P1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_104 ())). Qed.
Lemma avrF7P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_105 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P2 := BndP_Na_029.LibSegNa_avrF7P2.
Definition KS_avrF7P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P2.regs0 PavrF7P2.regs_out0).
Lemma KS_avrF7P2_0_ok : BG.kept_ok 60 PavrF7P2.regs0 PavrF7P2.regs_out0 KS_avrF7P2_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_106 ())). Qed.
Definition KS_avrF7P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P2.regs0 PavrF7P2.regs_out1).
Lemma KS_avrF7P2_1_ok : BG.kept_ok 60 PavrF7P2.regs0 PavrF7P2.regs_out1 KS_avrF7P2_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_107 ())). Qed.
Lemma avrF7P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_108 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P3 := BndP_Na_029.LibSegNa_avrF7P3.
Definition KS_avrF7P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P3.regs0 PavrF7P3.regs_out0).
Lemma KS_avrF7P3_0_ok : BG.kept_ok 60 PavrF7P3.regs0 PavrF7P3.regs_out0 KS_avrF7P3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_109 ())). Qed.
Definition KS_avrF7P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P3.regs0 PavrF7P3.regs_out1).
Lemma KS_avrF7P3_1_ok : BG.kept_ok 60 PavrF7P3.regs0 PavrF7P3.regs_out1 KS_avrF7P3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_110 ())). Qed.
Lemma avrF7P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 3
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_111 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P4 := BndP_Na_029.LibSegNa_avrF7P4.
Definition KS_avrF7P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P4.regs0 PavrF7P4.regs_out0).
Lemma KS_avrF7P4_0_ok : BG.kept_ok 60 PavrF7P4.regs0 PavrF7P4.regs_out0 KS_avrF7P4_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_112 ())). Qed.
Definition KS_avrF7P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P4.regs0 PavrF7P4.regs_out1).
Lemma KS_avrF7P4_1_ok : BG.kept_ok 60 PavrF7P4.regs0 PavrF7P4.regs_out1 KS_avrF7P4_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_113 ())). Qed.
Lemma avrF7P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_114 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P5 := BndP_Na_029.LibSegNa_avrF7P5.
Definition KS_avrF7P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P5.regs0 PavrF7P5.regs_out0).
Lemma KS_avrF7P5_0_ok : BG.kept_ok 60 PavrF7P5.regs0 PavrF7P5.regs_out0 KS_avrF7P5_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_115 ())). Qed.
Definition KS_avrF7P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P5.regs0 PavrF7P5.regs_out1).
Lemma KS_avrF7P5_1_ok : BG.kept_ok 60 PavrF7P5.regs0 PavrF7P5.regs_out1 KS_avrF7P5_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_116 ())). Qed.
Lemma avrF7P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_117 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P6 := BndP_Na_029.LibSegNa_avrF7P6.
Definition KS_avrF7P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P6.regs0 PavrF7P6.regs_out0).
Lemma KS_avrF7P6_0_ok : BG.kept_ok 60 PavrF7P6.regs0 PavrF7P6.regs_out0 KS_avrF7P6_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_118 ())). Qed.
Definition KS_avrF7P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P6.regs0 PavrF7P6.regs_out1).
Lemma KS_avrF7P6_1_ok : BG.kept_ok 60 PavrF7P6.regs0 PavrF7P6.regs_out1 KS_avrF7P6_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_119 ())). Qed.
Lemma avrF7P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 6
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_120 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrF7P7 := BndP_Na_029.LibSegNa_avrF7P7.
Definition KS_avrF7P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P7.regs0 PavrF7P7.regs_out0).
Lemma KS_avrF7P7_0_ok : BG.kept_ok 60 PavrF7P7.regs0 PavrF7P7.regs_out0 KS_avrF7P7_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_121 ())). Qed.
Definition KS_avrF7P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrF7P7.regs0 PavrF7P7.regs_out1).
Lemma KS_avrF7P7_1_ok : BG.kept_ok 60 PavrF7P7.regs0 PavrF7P7.regs_out1 KS_avrF7P7_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_122 ())). Qed.
Lemma avrF7P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> L5.u8_at RSEGS M ((V 33%nat) + 7) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 7) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd36dc M')
        /\ (forall x, In x KS_avrF7P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd36b4 M) (st fx' R' 0xd37d4 M')
        /\ (forall x, In x KS_avrF7P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 7)
        /\ getr R' (reg 11) = Z_to_bv 64 7
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ bv_unsigned (getr R' (reg 13)) = (Z.land (((V 33%nat) + 7) mod 2 ^ 64) 7)
        /\ getr R' (reg 23) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 36))
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EExt true 0 1 (EVar 36)) (ELit 0))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP3 ()) [] (Mh_0206_blobs1.kr_b_123 ())). Qed.
(* [comment removed for export] *)

End PECVALARP3.

End PnACValRP3.
Module PnACValRP4.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnACValRP4 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4;KS_avrR3Z_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4;KS_avrR3Z_1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z3ps1C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z3kn0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop04I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4>KS_avrR3Z_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR3Z6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4>KS_avrR3Z_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P1_1C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P13ps1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P2_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P29regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P2_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P2<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P23ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P23ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P2_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P26cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P2_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P4_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P49regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P4_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P43ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P43ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P43kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P4_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P46cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P4_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P5_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P59regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P5_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P53ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P53ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P53kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P5_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P56cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P5_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P6_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P69regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P6_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P63ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P63ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P63kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P6_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P66cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P6_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P7_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P79regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR3P7_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P73ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P73ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P73kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P7_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR3P76cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR3P7_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4;KS_avrR2Z_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4;KS_avrR2Z_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4>KS_avrR2Z_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR2Z6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4>KS_avrR2Z_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P2_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P29regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P2_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P23ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P23ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P2_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P26cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P2_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P4_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P49regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P4_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P43ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P43ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P43kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P4_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P46cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P4_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P5_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P59regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P5_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P53ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P53ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P53kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P5_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P56cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P5_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P6_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P69regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P6_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P63ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P63ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P63kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P6_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P66cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P6_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P7_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P79regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR2P7_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P73ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P73ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P73kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P7_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR2P76cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR2P7_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4;KS_avrR1Z_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4;KS_avrR1Z_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4>KS_avrR1Z_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP47PavrR1Z6cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4>KS_avrR1Z_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P2_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P29regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P2_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P23ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P23ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P23kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P2_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P26cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P2_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P4_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P49regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P4_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P43ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P43ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P43kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P4_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P46cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P4_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P5_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P59regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P5_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P53ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P53ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P53kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P5_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P56cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P5_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P69regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P6_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P69regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P6_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P6<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P63ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P63ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P63kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P6_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P66cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P6_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P79regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P7_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P79regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4<KS_avrR1P7_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P7<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P73ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P73ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P73kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P7_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP48PavrR1P76cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnACValRP4:PECVALARP4?KS_avrR1P7_1_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PECVALARP4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_124 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_125 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_126 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_127 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_128 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_129 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_130 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_131 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_132 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_133 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_134 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_135 ())). Qed.
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
Module PavrR3Z := BndP_Na_032.LibSegNa_avrR3Z.
Definition KS_avrR3Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3Z.regs0 PavrR3Z.regs_out0).
Lemma KS_avrR3Z_0_ok : BG.kept_ok 60 PavrR3Z.regs0 PavrR3Z.regs_out0 KS_avrR3Z_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_136 ())). Qed.
Definition KS_avrR3Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3Z.regs0 PavrR3Z.regs_out1).
Lemma KS_avrR3Z_1_ok : BG.kept_ok 60 PavrR3Z.regs0 PavrR3Z.regs_out1 KS_avrR3Z_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_137 ())). Qed.
Lemma avrR3Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 3) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_138 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P1 := BndP_Na_031.LibSegNa_avrR3P1.
Definition KS_avrR3P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P1.regs0 PavrR3P1.regs_out0).
Lemma KS_avrR3P1_0_ok : BG.kept_ok 60 PavrR3P1.regs0 PavrR3P1.regs_out0 KS_avrR3P1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_139 ())). Qed.
Definition KS_avrR3P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P1.regs0 PavrR3P1.regs_out1).
Lemma KS_avrR3P1_1_ok : BG.kept_ok 60 PavrR3P1.regs0 PavrR3P1.regs_out1 KS_avrR3P1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_140 ())). Qed.
Lemma avrR3P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_141 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P2 := BndP_Na_031.LibSegNa_avrR3P2.
Definition KS_avrR3P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P2.regs0 PavrR3P2.regs_out0).
Lemma KS_avrR3P2_0_ok : BG.kept_ok 60 PavrR3P2.regs0 PavrR3P2.regs_out0 KS_avrR3P2_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_142 ())). Qed.
Definition KS_avrR3P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P2.regs0 PavrR3P2.regs_out1).
Lemma KS_avrR3P2_1_ok : BG.kept_ok 60 PavrR3P2.regs0 PavrR3P2.regs_out1 KS_avrR3P2_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_143 ())). Qed.
Lemma avrR3P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_144 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P3 := BndP_Na_031.LibSegNa_avrR3P3.
Definition KS_avrR3P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P3.regs0 PavrR3P3.regs_out0).
Lemma KS_avrR3P3_0_ok : BG.kept_ok 60 PavrR3P3.regs0 PavrR3P3.regs_out0 KS_avrR3P3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_145 ())). Qed.
Definition KS_avrR3P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P3.regs0 PavrR3P3.regs_out1).
Lemma KS_avrR3P3_1_ok : BG.kept_ok 60 PavrR3P3.regs0 PavrR3P3.regs_out1 KS_avrR3P3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_146 ())). Qed.
Lemma avrR3P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_147 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P4 := BndP_Na_032.LibSegNa_avrR3P4.
Definition KS_avrR3P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P4.regs0 PavrR3P4.regs_out0).
Lemma KS_avrR3P4_0_ok : BG.kept_ok 60 PavrR3P4.regs0 PavrR3P4.regs_out0 KS_avrR3P4_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_148 ())). Qed.
Definition KS_avrR3P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P4.regs0 PavrR3P4.regs_out1).
Lemma KS_avrR3P4_1_ok : BG.kept_ok 60 PavrR3P4.regs0 PavrR3P4.regs_out1 KS_avrR3P4_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_149 ())). Qed.
Lemma avrR3P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_150 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P5 := BndP_Na_032.LibSegNa_avrR3P5.
Definition KS_avrR3P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P5.regs0 PavrR3P5.regs_out0).
Lemma KS_avrR3P5_0_ok : BG.kept_ok 60 PavrR3P5.regs0 PavrR3P5.regs_out0 KS_avrR3P5_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_151 ())). Qed.
Definition KS_avrR3P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P5.regs0 PavrR3P5.regs_out1).
Lemma KS_avrR3P5_1_ok : BG.kept_ok 60 PavrR3P5.regs0 PavrR3P5.regs_out1 KS_avrR3P5_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_152 ())). Qed.
Lemma avrR3P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_153 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P6 := BndP_Na_032.LibSegNa_avrR3P6.
Definition KS_avrR3P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P6.regs0 PavrR3P6.regs_out0).
Lemma KS_avrR3P6_0_ok : BG.kept_ok 60 PavrR3P6.regs0 PavrR3P6.regs_out0 KS_avrR3P6_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_154 ())). Qed.
Definition KS_avrR3P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P6.regs0 PavrR3P6.regs_out1).
Lemma KS_avrR3P6_1_ok : BG.kept_ok 60 PavrR3P6.regs0 PavrR3P6.regs_out1 KS_avrR3P6_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_155 ())). Qed.
Lemma avrR3P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 5 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_156 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR3P7 := BndP_Na_032.LibSegNa_avrR3P7.
Definition KS_avrR3P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P7.regs0 PavrR3P7.regs_out0).
Lemma KS_avrR3P7_0_ok : BG.kept_ok 60 PavrR3P7.regs0 PavrR3P7.regs_out0 KS_avrR3P7_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_157 ())). Qed.
Definition KS_avrR3P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR3P7.regs0 PavrR3P7.regs_out1).
Lemma KS_avrR3P7_1_ok : BG.kept_ok 60 PavrR3P7.regs0 PavrR3P7.regs_out1 KS_avrR3P7_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_158 ())). Qed.
Lemma avrR3P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 4) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 3) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 3) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7) <= 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR3P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3734 M) (st fx' R' 0xd3750 M')
        /\ (forall x, In x KS_avrR3P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 3) mod 2 ^ 64) 7)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 33%nat) + 3)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_159 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2Z := BndP_Na_031.LibSegNa_avrR2Z.
Definition KS_avrR2Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2Z.regs0 PavrR2Z.regs_out0).
Lemma KS_avrR2Z_0_ok : BG.kept_ok 60 PavrR2Z.regs0 PavrR2Z.regs_out0 KS_avrR2Z_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_160 ())). Qed.
Definition KS_avrR2Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2Z.regs0 PavrR2Z.regs_out1).
Lemma KS_avrR2Z_1_ok : BG.kept_ok 60 PavrR2Z.regs0 PavrR2Z.regs_out1 KS_avrR2Z_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_161 ())). Qed.
Lemma avrR2Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 2) / 8) + 2147450880) 1 -> 0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_162 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P1 := BndP_Na_031.LibSegNa_avrR2P1.
Definition KS_avrR2P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P1.regs0 PavrR2P1.regs_out0).
Lemma KS_avrR2P1_0_ok : BG.kept_ok 60 PavrR2P1.regs0 PavrR2P1.regs_out0 KS_avrR2P1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_163 ())). Qed.
Definition KS_avrR2P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P1.regs0 PavrR2P1.regs_out1).
Lemma KS_avrR2P1_1_ok : BG.kept_ok 60 PavrR2P1.regs0 PavrR2P1.regs_out1 KS_avrR2P1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_164 ())). Qed.
Lemma avrR2P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 0 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_165 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P2 := BndP_Na_031.LibSegNa_avrR2P2.
Definition KS_avrR2P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P2.regs0 PavrR2P2.regs_out0).
Lemma KS_avrR2P2_0_ok : BG.kept_ok 60 PavrR2P2.regs0 PavrR2P2.regs_out0 KS_avrR2P2_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_166 ())). Qed.
Definition KS_avrR2P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P2.regs0 PavrR2P2.regs_out1).
Lemma KS_avrR2P2_1_ok : BG.kept_ok 60 PavrR2P2.regs0 PavrR2P2.regs_out1 KS_avrR2P2_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_167 ())). Qed.
Lemma avrR2P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 1 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_168 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P3 := BndP_Na_031.LibSegNa_avrR2P3.
Definition KS_avrR2P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P3.regs0 PavrR2P3.regs_out0).
Lemma KS_avrR2P3_0_ok : BG.kept_ok 60 PavrR2P3.regs0 PavrR2P3.regs_out0 KS_avrR2P3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_169 ())). Qed.
Definition KS_avrR2P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P3.regs0 PavrR2P3.regs_out1).
Lemma KS_avrR2P3_1_ok : BG.kept_ok 60 PavrR2P3.regs0 PavrR2P3.regs_out1 KS_avrR2P3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_170 ())). Qed.
Lemma avrR2P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 2 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_171 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P4 := BndP_Na_031.LibSegNa_avrR2P4.
Definition KS_avrR2P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P4.regs0 PavrR2P4.regs_out0).
Lemma KS_avrR2P4_0_ok : BG.kept_ok 60 PavrR2P4.regs0 PavrR2P4.regs_out0 KS_avrR2P4_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_172 ())). Qed.
Definition KS_avrR2P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P4.regs0 PavrR2P4.regs_out1).
Lemma KS_avrR2P4_1_ok : BG.kept_ok 60 PavrR2P4.regs0 PavrR2P4.regs_out1 KS_avrR2P4_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_173 ())). Qed.
Lemma avrR2P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 3 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_174 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P5 := BndP_Na_031.LibSegNa_avrR2P5.
Definition KS_avrR2P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P5.regs0 PavrR2P5.regs_out0).
Lemma KS_avrR2P5_0_ok : BG.kept_ok 60 PavrR2P5.regs0 PavrR2P5.regs_out0 KS_avrR2P5_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_175 ())). Qed.
Definition KS_avrR2P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P5.regs0 PavrR2P5.regs_out1).
Lemma KS_avrR2P5_1_ok : BG.kept_ok 60 PavrR2P5.regs0 PavrR2P5.regs_out1 KS_avrR2P5_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_176 ())). Qed.
Lemma avrR2P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 4 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_177 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P6 := BndP_Na_031.LibSegNa_avrR2P6.
Definition KS_avrR2P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P6.regs0 PavrR2P6.regs_out0).
Lemma KS_avrR2P6_0_ok : BG.kept_ok 60 PavrR2P6.regs0 PavrR2P6.regs_out0 KS_avrR2P6_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_178 ())). Qed.
Definition KS_avrR2P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P6.regs0 PavrR2P6.regs_out1).
Lemma KS_avrR2P6_1_ok : BG.kept_ok 60 PavrR2P6.regs0 PavrR2P6.regs_out1 KS_avrR2P6_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_179 ())). Qed.
Lemma avrR2P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 5 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_180 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR2P7 := BndP_Na_031.LibSegNa_avrR2P7.
Definition KS_avrR2P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P7.regs0 PavrR2P7.regs_out0).
Lemma KS_avrR2P7_0_ok : BG.kept_ok 60 PavrR2P7.regs0 PavrR2P7.regs_out0 KS_avrR2P7_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_181 ())). Qed.
Definition KS_avrR2P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR2P7.regs0 PavrR2P7.regs_out1).
Lemma KS_avrR2P7_1_ok : BG.kept_ok 60 PavrR2P7.regs0 PavrR2P7.regs_out1 KS_avrR2P7_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_182 ())). Qed.
Lemma avrR2P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 33%nat) + 3) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 2) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 2) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7) <= 6 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR2P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd3750 M) (st fx' R' 0xd376c M')
        /\ (forall x, In x KS_avrR2P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 2)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 2) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_183 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1Z := BndP_Na_031.LibSegNa_avrR1Z.
Definition KS_avrR1Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1Z.regs0 PavrR1Z.regs_out0).
Lemma KS_avrR1Z_0_ok : BG.kept_ok 60 PavrR1Z.regs0 PavrR1Z.regs_out0 KS_avrR1Z_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_184 ())). Qed.
Definition KS_avrR1Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1Z.regs0 PavrR1Z.regs_out1).
Lemma KS_avrR1Z_1_ok : BG.kept_ok 60 PavrR1Z.regs0 PavrR1Z.regs_out1 KS_avrR1Z_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_185 ())). Qed.
Lemma avrR1Z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5KA.zeros_at M ((((V 33%nat) + 1) / 8) + 2147450880) 1 -> 0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1Z_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1Z_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_186 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P1 := BndP_Na_030.LibSegNa_avrR1P1.
Definition KS_avrR1P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P1.regs0 PavrR1P1.regs_out0).
Lemma KS_avrR1P1_0_ok : BG.kept_ok 60 PavrR1P1.regs0 PavrR1P1.regs_out0 KS_avrR1P1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_187 ())). Qed.
Definition KS_avrR1P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P1.regs0 PavrR1P1.regs_out1).
Lemma KS_avrR1P1_1_ok : BG.kept_ok 60 PavrR1P1.regs0 PavrR1P1.regs_out1 KS_avrR1P1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_188 ())). Qed.
Lemma avrR1P1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 1 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 0 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_189 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P2 := BndP_Na_030.LibSegNa_avrR1P2.
Definition KS_avrR1P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P2.regs0 PavrR1P2.regs_out0).
Lemma KS_avrR1P2_0_ok : BG.kept_ok 60 PavrR1P2.regs0 PavrR1P2.regs_out0 KS_avrR1P2_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_190 ())). Qed.
Definition KS_avrR1P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P2.regs0 PavrR1P2.regs_out1).
Lemma KS_avrR1P2_1_ok : BG.kept_ok 60 PavrR1P2.regs0 PavrR1P2.regs_out1 KS_avrR1P2_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_191 ())). Qed.
Lemma avrR1P2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 2 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 1 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_192 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P3 := BndP_Na_030.LibSegNa_avrR1P3.
Definition KS_avrR1P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P3.regs0 PavrR1P3.regs_out0).
Lemma KS_avrR1P3_0_ok : BG.kept_ok 60 PavrR1P3.regs0 PavrR1P3.regs_out0 KS_avrR1P3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_193 ())). Qed.
Definition KS_avrR1P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P3.regs0 PavrR1P3.regs_out1).
Lemma KS_avrR1P3_1_ok : BG.kept_ok 60 PavrR1P3.regs0 PavrR1P3.regs_out1 KS_avrR1P3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_194 ())). Qed.
Lemma avrR1P3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 3 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 2 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_195 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P4 := BndP_Na_030.LibSegNa_avrR1P4.
Definition KS_avrR1P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P4.regs0 PavrR1P4.regs_out0).
Lemma KS_avrR1P4_0_ok : BG.kept_ok 60 PavrR1P4.regs0 PavrR1P4.regs_out0 KS_avrR1P4_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_196 ())). Qed.
Definition KS_avrR1P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P4.regs0 PavrR1P4.regs_out1).
Lemma KS_avrR1P4_1_ok : BG.kept_ok 60 PavrR1P4.regs0 PavrR1P4.regs_out1 KS_avrR1P4_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_197 ())). Qed.
Lemma avrR1P4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 4 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 3 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_198 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P5 := BndP_Na_030.LibSegNa_avrR1P5.
Definition KS_avrR1P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P5.regs0 PavrR1P5.regs_out0).
Lemma KS_avrR1P5_0_ok : BG.kept_ok 60 PavrR1P5.regs0 PavrR1P5.regs_out0 KS_avrR1P5_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_199 ())). Qed.
Definition KS_avrR1P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P5.regs0 PavrR1P5.regs_out1).
Lemma KS_avrR1P5_1_ok : BG.kept_ok 60 PavrR1P5.regs0 PavrR1P5.regs_out1 KS_avrR1P5_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_200 ())). Qed.
Lemma avrR1P5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 5 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 4 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P5_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P5_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_201 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P6 := BndP_Na_031.LibSegNa_avrR1P6.
Definition KS_avrR1P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P6.regs0 PavrR1P6.regs_out0).
Lemma KS_avrR1P6_0_ok : BG.kept_ok 60 PavrR1P6.regs0 PavrR1P6.regs_out0 KS_avrR1P6_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_202 ())). Qed.
Definition KS_avrR1P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P6.regs0 PavrR1P6.regs_out1).
Lemma KS_avrR1P6_1_ok : BG.kept_ok 60 PavrR1P6.regs0 PavrR1P6.regs_out1 KS_avrR1P6_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_203 ())). Qed.
Lemma avrR1P6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 6 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 5 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P6_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P6_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_204 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavrR1P7 := BndP_Na_031.LibSegNa_avrR1P7.
Definition KS_avrR1P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P7.regs0 PavrR1P7.regs_out0).
Lemma KS_avrR1P7_0_ok : BG.kept_ok 60 PavrR1P7.regs0 PavrR1P7.regs_out0 KS_avrR1P7_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_205 ())). Qed.
Definition KS_avrR1P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 PavrR1P7.regs0 PavrR1P7.regs_out1).
Lemma KS_avrR1P7_1_ok : BG.kept_ok 60 PavrR1P7.regs0 PavrR1P7.regs_out1 KS_avrR1P7_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_206 ())). Qed.
Lemma avrR1P7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 5) = Z_to_bv 64 245 -> getr R (reg 6) = Z_to_bv 64 (-65) -> getr R (reg 7) = Z_to_bv 64 239 -> getr R (reg 8) = Z_to_bv 64 240 -> getr R (reg 9) = Z_to_bv 64 144 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 33%nat) + 2) -> getr R (reg 14) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 15) = Z_to_bv 64 8 -> getr R (reg 16) = Z_to_bv 64 1 -> getr R (reg 17) = Z_to_bv 64 (-62) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 244 -> getr R (reg 20) = Z_to_bv 64 143 -> getr R (reg 21) = Z_to_bv 64 2 -> getr R (reg 22) = Z_to_bv 64 3 -> getr R (reg 23) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 37%nat) -> getr R (reg 28) = Z_to_bv 64 224 -> getr R (reg 29) = Z_to_bv 64 160 -> getr R (reg 30) = Z_to_bv 64 237 -> getr R (reg 31) = Z_to_bv 64 159 ->
  0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 35%nat) <= 67108864 -> 1 <= ((V 33%nat) + (V 35%nat)) <= 140737488355328 -> 0 <= (V 37%nat) <= 255 ->
  L5.u8_at RSEGS M ((V 33%nat) + 1) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> L5.u8_at RSEGS M ((((V 33%nat) + 1) / 8) + 2147450880) 7 -> 0 <= (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7) <= 6 ->
  0 <= (V 34%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3890 M')
        /\ (forall x, In x KS_avrR1P7_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 1)
      \/ (msteps RSEGS (st fx R 0xd376c M) (st fx' R' 0xd3788 M')
        /\ (forall x, In x KS_avrR1P7_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 0 1 (EVar 39))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 1)
        /\ bv_unsigned (getr R' (reg 25)) = (Z.land (((V 33%nat) + 1) mod 2 ^ 64) 7)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (ELit (-65)) (EExt true 0 1 (EVar 39)))) <= 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACValRP4 ()) [] (Mh_0206_blobs1.kr_b_207 ())). Qed.
(* [comment removed for export] *)

End PECVALARP4.

End PnACValRP4.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0166.
Module PnAEncBstP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0166. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0166 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAEncBstP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtA8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA8<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InK4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA86cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA83kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtA83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtA8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtB8C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtB83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtB8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtJ8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtJ83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtJ8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP9KS_abtA16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP<KS_abtA16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP9KS_abtW16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP<KS_abtW16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP9KS_abtA32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA326cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtA323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP<KS_abtA32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP9KS_abtW32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtW323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP<KS_abtW32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP9KS_abtJ32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtJ323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP<KS_abtJ32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtL0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtL0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtL1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtL13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtL1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7KS_abtBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP:KS_abtB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7KS_abtNC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtN3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP:KS_abtN_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7KS_abtEC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP5PabtE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP:KS_abtE_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtV0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtV0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP8KS_abtV1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV13NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP;KS_abtV1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP6PabtV16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP9KS_abtV1wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP<KS_abtV1w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206:PnAEncBstP8PNAENBTP7PabtV1w6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNAENBTP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_208 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_209 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_210 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_211 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_212 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_213 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_214 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_215 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_216 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_217 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_218 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_219 ())). Qed.
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
Module PabtA8 := BndP_Na_002.LibSegNa_abtA8.
Definition KS_abtA8 : list nat := Eval vm_compute in (BG.kept_list 60 PabtA8.regs0 PabtA8.regs_out0).
Lemma KS_abtA8_ok : BG.kept_ok 60 PabtA8.regs0 PabtA8.regs_out0 KS_abtA8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_220 ())). Qed.
Lemma abtA8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 7 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 80)) ->
  L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 255 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 80)) ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 11))) + 8) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3c7c M) (st fx' R' 0xc6a1c M')
        /\ (forall x, In x KS_abtA8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802116
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 77)
        /\ getr R' (reg 12) = Z_to_bv 64 1440376
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 ((bv_unsigned (getr R (reg 11))) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 11))) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_221 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtB8 := BndP_Na_002.LibSegNa_abtB8.
Definition KS_abtB8 : list nat := Eval vm_compute in (BG.kept_list 60 PabtB8.regs0 PabtB8.regs_out0).
Lemma KS_abtB8_ok : BG.kept_ok 60 PabtB8.regs0 PabtB8.regs_out0 KS_abtB8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_222 ())). Qed.
Lemma abtB8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4104 <= (V 36%nat) <= 140737488355280 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 36%nat) (V 41%nat) -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 34%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 76) <= bv_unsigned a < ((V 2%nat) - 76) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 76) <= i < ((V 2%nat) - 76) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d44 M) (st fx' R' 0xc6a1c M')
        /\ (forall x, In x KS_abtB8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802140
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 76)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_223 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtJ8 := BndP_Na_002.LibSegNa_abtJ8.
Definition KS_abtJ8 : list nat := Eval vm_compute in (BG.kept_list 60 PabtJ8.regs0 PabtJ8.regs_out0).
Lemma KS_abtJ8_ok : BG.kept_ok 60 PabtJ8.regs0 PabtJ8.regs_out0 KS_abtJ8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_224 ())). Qed.
Lemma abtJ8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d5c M) (st fx' R' 0xc3d90 M')
        /\ (forall x, In x KS_abtJ8 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_225 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtA16 := BndP_Na_002.LibSegNa_abtA16.
Definition KS_abtA16 : list nat := Eval vm_compute in (BG.kept_list 60 PabtA16.regs0 PabtA16.regs_out0).
Lemma KS_abtA16_ok : BG.kept_ok 60 PabtA16.regs0 PabtA16.regs_out0 KS_abtA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_226 ())). Qed.
Lemma abtA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 7 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 80)) ->
  L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 256 <= (V 34%nat) <= 65535 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 80)) ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 11))) + 8) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3c7c M) (st fx' R' 0xc6a1c M')
        /\ (forall x, In x KS_abtA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802180
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 75)
        /\ getr R' (reg 12) = Z_to_bv 64 1440376
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 ((bv_unsigned (getr R (reg 11))) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 11))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_227 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtW16 := BndP_Na_003.LibSegNa_abtW16.
Definition KS_abtW16 : list nat := Eval vm_compute in (BG.kept_list 60 PabtW16.regs0 PabtW16.regs_out0).
Lemma KS_abtW16_ok : BG.kept_ok 60 PabtW16.regs0 PabtW16.regs_out0 KS_abtW16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_228 ())). Qed.
Lemma abtW16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d84 M) (st fx' R' 0xc62d8 M')
        /\ (forall x, In x KS_abtW16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802192
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_229 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtA32 := BndP_Na_002.LibSegNa_abtA32.
Definition KS_abtA32 : list nat := Eval vm_compute in (BG.kept_list 60 PabtA32.regs0 PabtA32.regs_out0).
Lemma KS_abtA32_ok : BG.kept_ok 60 PabtA32.regs0 PabtA32.regs_out0 KS_abtA32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_230 ())). Qed.
Lemma abtA32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4096 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 10))) / 8) + 2147450880) 7 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 80)) ->
  L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 10))) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 4096 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 65536 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 80) + 80 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 80)) ->
  (2147446784 + 17592186048512 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= 2147446784) -> L5KA.zeros_at M (((bv_unsigned (getr R (reg 11))) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((bv_unsigned (getr R (reg 11))) + 8) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3c7c M) (st fx' R' 0xc6a1c M')
        /\ (forall x, In x KS_abtA32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802064
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 74)
        /\ getr R' (reg 12) = Z_to_bv 64 1440376
        /\ getr R' (reg 18) = getr R (reg 11)
        /\ getr R' (reg 19) = Z_to_bv 64 ((bv_unsigned (getr R (reg 11))) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((bv_unsigned (getr R (reg 11))) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_231 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtW32 := BndP_Na_003.LibSegNa_abtW32.
Definition KS_abtW32 : list nat := Eval vm_compute in (BG.kept_list 60 PabtW32.regs0 PabtW32.regs_out0).
Lemma KS_abtW32_ok : BG.kept_ok 60 PabtW32.regs0 PabtW32.regs_out0 KS_abtW32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_232 ())). Qed.
Lemma abtW32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d10 M) (st fx' R' 0xc636c M')
        /\ (forall x, In x KS_abtW32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802076
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_233 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtJ32 := BndP_Na_002.LibSegNa_abtJ32.
Definition KS_abtJ32 : list nat := Eval vm_compute in (BG.kept_list 60 PabtJ32.regs0 PabtJ32.regs_out0).
Lemma KS_abtJ32_ok : BG.kept_ok 60 PabtJ32.regs0 PabtJ32.regs_out0 KS_abtJ32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_234 ())). Qed.
Lemma abtJ32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d1c M) (st fx' R' 0xc3d90 M')
        /\ (forall x, In x KS_abtJ32 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_235 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtL0 := BndP_Na_003.LibSegNa_abtL0.
Definition KS_abtL0 : list nat := Eval vm_compute in (BG.kept_list 60 PabtL0.regs0 PabtL0.regs_out0).
Lemma KS_abtL0_ok : BG.kept_ok 60 PabtL0.regs0 PabtL0.regs_out0 KS_abtL0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_236 ())). Qed.
Lemma abtL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 4096 <= (V 11%nat) <= 140737488355312 -> 4104 <= (V 35%nat) <= 140737488355320 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M (V 35%nat) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 0 -> (((V 2%nat) - 80) + 80 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 80)) ->
  (((V 2%nat) - 80) + 80 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 80)) -> (2147446784 + 17592186048512 <= (V 11%nat) \/ (V 11%nat) + 16 <= 2147446784) -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 11%nat) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d90 M) (st fx' R' 0xc3e10 M')
        /\ (forall x, In x KS_abtL0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_237 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtL1 := BndP_Na_003.LibSegNa_abtL1.
Definition KS_abtL1 : list nat := Eval vm_compute in (BG.kept_list 60 PabtL1.regs0 PabtL1.regs_out0).
Lemma KS_abtL1_ok : BG.kept_ok 60 PabtL1.regs0 PabtL1.regs_out0 KS_abtL1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_238 ())). Qed.
Lemma abtL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 11%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 4104 <= (V 36%nat) <= 140737488355280 -> 4096 <= (V 11%nat) <= 140737488355312 -> 4104 <= (V 35%nat) <= 140737488355320 ->
  L5.u64_at RSEGS M (V 11%nat) (V 33%nat) -> L5.u64_at RSEGS M (V 35%nat) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 ->
  (((V 2%nat) - 80) + 80 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 80)) -> (((V 2%nat) - 80) + 80 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 80)) -> (2147446784 + 17592186048512 <= (V 11%nat) \/ (V 11%nat) + 16 <= 2147446784) -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 11%nat) / 8) + 2147450880) 1 -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3d90 M) (st fx' R' 0xc3dc0 M')
        /\ (forall x, In x KS_abtL1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_239 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtB := BndP_Na_002.LibSegNa_abtB.
Definition KS_abtB : list nat := Eval vm_compute in (BG.kept_list 60 PabtB.regs0 PabtB.regs_out0).
Lemma KS_abtB_ok : BG.kept_ok 60 PabtB.regs0 PabtB.regs_out0 KS_abtB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_240 ())). Qed.
Lemma abtB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 39%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 39%nat) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4104 <= (V 36%nat) <= 140737488355280 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M (V 36%nat) (V 41%nat) -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 1 <= (V 39%nat) <= 140737488355327 -> L5.u8_at RSEGS M (V 39%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> (((V 2%nat) - 80) + 80 <= (V 39%nat) \/ (V 39%nat) + 1 <= ((V 2%nat) - 80)) -> 1 <= (V 38%nat) <= 536870911 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 73) <= bv_unsigned a < ((V 2%nat) - 73) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 73) <= i < ((V 2%nat) - 73) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3dd0 M) (st fx' R' 0xc6a1c M')
        /\ (forall x, In x KS_abtB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802284
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 73)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_241 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtN := BndP_Na_003.LibSegNa_abtN.
Definition KS_abtN : list nat := Eval vm_compute in (BG.kept_list 60 PabtN.regs0 PabtN.regs_out0).
Lemma KS_abtN_ok : BG.kept_ok 60 PabtN.regs0 PabtN.regs_out0 KS_abtN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_242 ())). Qed.
Lemma abtN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 39%nat) -> getr R (reg 19) = Z_to_bv 64 (V 38%nat) -> getr R (reg 20) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 39%nat) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 1 <= (V 39%nat) <= 140737488355327 -> 2 <= (V 38%nat) <= 536870911 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3dec M) (st fx' R' 0xc3dc0 M')
        /\ (forall x, In x KS_abtN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 39%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 38%nat) - 1)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 39%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_243 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtE := BndP_Na_002.LibSegNa_abtE.
Definition KS_abtE : list nat := Eval vm_compute in (BG.kept_list 60 PabtE.regs0 PabtE.regs_out0).
Lemma KS_abtE_ok : BG.kept_ok 60 PabtE.regs0 PabtE.regs_out0 KS_abtE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_244 ())). Qed.
Lemma abtE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 39%nat) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 39%nat) ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> 1 <= (V 39%nat) <= 140737488355327 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3dec M) (st fx' R' 0xc3e10 M')
        /\ (forall x, In x KS_abtE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 39%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 39%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_245 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtV0 := BndP_Na_003.LibSegNa_abtV0.
Definition KS_abtV0 : list nat := Eval vm_compute in (BG.kept_list 60 PabtV0.regs0 PabtV0.regs_out0).
Lemma KS_abtV0_ok : BG.kept_ok 60 PabtV0.regs0 PabtV0.regs_out0 KS_abtV0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_246 ())). Qed.
Lemma abtV0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 80)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) ->
  0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3e10 M) (st fx' R' 0xc3e90 M')
        /\ (forall x, In x KS_abtV0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_247 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtV1 := BndP_Na_003.LibSegNa_abtV1.
Definition KS_abtV1 : list nat := Eval vm_compute in (BG.kept_list 60 PabtV1.regs0 PabtV1.regs_out0).
Lemma KS_abtV1_ok : BG.kept_ok 60 PabtV1.regs0 PabtV1.regs_out0 KS_abtV1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_248 ())). Qed.
Lemma abtV1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 80)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 80) \/ ((V 2%nat) - 80) + 80 <= ((V 39%nat) - 24)) ->
  (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3e10 M) (st fx' R' 0xc3e90 M')
        /\ (forall x, In x KS_abtV1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_249 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabtV1w := BndP_Na_003.LibSegNa_abtV1w.
Definition KS_abtV1w : list nat := Eval vm_compute in (BG.kept_list 60 PabtV1w.regs0 PabtV1w.regs_out0).
Lemma KS_abtV1w_ok : BG.kept_ok 60 PabtV1w.regs0 PabtV1w.regs_out0 KS_abtV1w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_250 ())). Qed.
Lemma abtV1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1376256 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 80) + 80 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 80)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 24 <= ((V 39%nat) - (V 38%nat)) <= 100000 ->
  L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 8) / 8) + 2147450880) 1 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 80) \/ ((V 2%nat) - 80) + 80 <= ((V 39%nat) - 24)) ->
  (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc3e10 M) (st fx' R' 0xc3e90 M')
        /\ (forall x, In x KS_abtV1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncBstP ()) [] (Mh_0206_blobs1.kr_b_251 ())). Qed.
(* [comment removed for export] *)

End PNAENBTP.

End PnAEncBstP.
Module PnAEncTobdP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAEncTobdP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdA0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA03NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdA0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP9KS_atdA16C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA16<seg_sound_axC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP<KS_atdA16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP9KS_atdB_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB9regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP9KS_atdB_1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega:ZMicromega;ZArithProof03c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0;C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28evars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zc_sound'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?range_of_KRangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0I47Corelib4Init9Datatypes7reflect00c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP>u8_of_KWord1maC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB3ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB3ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdB3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP<KS_atdB_0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop02I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP<KS_atdB_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdZ1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdZ1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ19regs_out2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdZ1_2C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ1<seg_sound_axC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapK69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za03C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13F0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdZ1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ16cells1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13ps1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdZ1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ16cells2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZ13ps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdZ1_2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdZAC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdZA_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdZBC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdZB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdZCC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdZC3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdZC_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdD0_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD09regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdD0_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD03ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD03ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdD0_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD06cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdD0_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdD1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdD1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdD2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdD2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdD3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdD33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdD3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdL1_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL19regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdL1_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL13ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL13ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdL1_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL16cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdL1_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdL2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdL2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdL3_0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL39regs_out1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdL3_1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL33ps0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL33ps1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL33kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdL3_0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdL36cells0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP=KS_atdL3_1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP9KS_atdDNpC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNp3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP<KS_atdDNp_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP9KS_atdDNnC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn<seg_sound_axC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP<setbit1_byteC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP<KS_atdDNn_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7PatdDNn6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdTiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@land1_bit0_falseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi3NX0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTi3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdTi_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP8KS_atdTdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP6PatdTd3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP;KS_atdTd_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7KS_atdUC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdU3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdU_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP7KS_atdXC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP5PatdX3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206;PnAEncTobdP8PNAETBDP:KS_atdX_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNAETBDP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_252 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_253 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_254 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_255 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_256 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_257 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_258 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_259 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_260 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_261 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_262 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_263 ())). Qed.
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
Module PatdA0 := BndP_Na_011.LibSegNa_atdA0.
Definition KS_atdA0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdA0.regs0 PatdA0.regs_out0).
Lemma KS_atdA0_ok : BG.kept_ok 80 PatdA0.regs0 PatdA0.regs_out0 KS_atdA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_264 ())). Qed.
Lemma atdA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9210 M) (st fx' R' 0x64af0 M')
        /\ (forall x, In x KS_atdA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 823948
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 12)
        /\ getr R' (reg 20) = getr R (reg 13)
        /\ getr R' (reg 22) = getr R (reg 10)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_265 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdA16 := BndP_Na_011.LibSegNa_atdA16.
Definition KS_atdA16 : list nat := Eval vm_compute in (BG.kept_list 80 PatdA16.regs0 PatdA16.regs_out0).
Lemma KS_atdA16_ok : BG.kept_ok 80 PatdA16.regs0 PatdA16.regs_out0 KS_atdA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_266 ())). Qed.
Lemma atdA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 176) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 176) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9210 M) (st fx' R' 0x64af0 M')
        /\ (forall x, In x KS_atdA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 823948
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 12)
        /\ getr R' (reg 20) = getr R (reg 13)
        /\ getr R' (reg 22) = getr R (reg 10)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_267 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdB := BndP_Na_011.LibSegNa_atdB.
Definition KS_atdB_0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdB.regs0 PatdB.regs_out0).
Lemma KS_atdB_0_ok : BG.kept_ok 80 PatdB.regs0 PatdB.regs_out0 KS_atdB_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_268 ())). Qed.
Definition KS_atdB_1 : list nat := Eval vm_compute in (BG.kept_list 80 PatdB.regs0 PatdB.regs_out1).
Lemma KS_atdB_1_ok : BG.kept_ok 80 PatdB.regs0 PatdB.regs_out1 KS_atdB_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_269 ())). Qed.
Lemma atdB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 0 <= (V 12%nat) <= 1 ->
  L5.writable RSEGS M ((V 2%nat) - 152) 48 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 50%nat) 24 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 48) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 48) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xc928c M) (st fx' R' 0xc9370 M')
        /\ (forall x, In x KS_atdB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 48
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat))
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 50%nat) + 96)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 12%nat)
        /\ 1 <= (((V 11%nat) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat))
      \/ (msteps RSEGS (st fx R 0xc928c M) (st fx' R' 0xc9538 M')
        /\ (forall x, In x KS_atdB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 12) = Z_to_bv 64 823824
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 22
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 50%nat)
        /\ (((V 11%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_270 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdZ1 := BndP_Na_012.LibSegNa_atdZ1.
Definition KS_atdZ1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdZ1.regs0 PatdZ1.regs_out0).
Lemma KS_atdZ1_0_ok : BG.kept_ok 80 PatdZ1.regs0 PatdZ1.regs_out0 KS_atdZ1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_271 ())). Qed.
Definition KS_atdZ1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PatdZ1.regs0 PatdZ1.regs_out1).
Lemma KS_atdZ1_1_ok : BG.kept_ok 80 PatdZ1.regs0 PatdZ1.regs_out1 KS_atdZ1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_272 ())). Qed.
Definition KS_atdZ1_2 : list nat := Eval vm_compute in (BG.kept_list 80 PatdZ1.regs0 PatdZ1.regs_out2).
Lemma KS_atdZ1_2_ok : BG.kept_ok 80 PatdZ1.regs0 PatdZ1.regs_out2 KS_atdZ1_2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_273 ())). Qed.
Lemma atdZ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 48 -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 4096 <= (V 36%nat) <= 140737488355327 ->
  L5.u8_at RSEGS M (V 36%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 1 <= (((V 10%nat) + (V 11%nat)) - (V 36%nat)) <= 31 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xc9380 M) (st fx' R' 0xc93a4 M')
        /\ (forall x, In x KS_atdZ1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ 1 <= (((V 37%nat) - 48) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xc9380 M) (st fx' R' 0xc9370 M')
        /\ (forall x, In x KS_atdZ1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ (((V 36%nat) + 1) mod 2 ^ 64) < (((V 10%nat) + (V 11%nat)) mod 2 ^ 64)
        /\ (((V 37%nat) - 48) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xc9380 M) (st fx' R' 0xc93a4 M')
        /\ (forall x, In x KS_atdZ1_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ (((V 10%nat) + (V 11%nat)) mod 2 ^ 64) <= (((V 36%nat) + 1) mod 2 ^ 64)
        /\ (((V 37%nat) - 48) mod 2 ^ 64) < 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_274 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdZA := BndP_Na_012.LibSegNa_atdZA.
Definition KS_atdZA : list nat := Eval vm_compute in (BG.kept_list 80 PatdZA.regs0 PatdZA.regs_out0).
Lemma KS_atdZA_ok : BG.kept_ok 80 PatdZA.regs0 PatdZA.regs_out0 KS_atdZA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_275 ())). Qed.
Lemma atdZA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 12) = Z_to_bv 64 48 -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 32 ->
  L5.writable RSEGS M ((V 50%nat) + 32) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc93a4 M) (st fx' R' 0x7f058 M')
        /\ (forall x, In x KS_atdZA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824284
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 40)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 24
        /\ L5.u8_at RSEGS M' ((V 50%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_276 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdZB := BndP_Na_012.LibSegNa_atdZB.
Definition KS_atdZB : list nat := Eval vm_compute in (BG.kept_list 80 PatdZB.regs0 PatdZB.regs_out0).
Lemma KS_atdZB_ok : BG.kept_ok 80 PatdZB.regs0 PatdZB.regs_out0 KS_atdZB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_277 ())). Qed.
Lemma atdZB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc93dc M) (st fx' R' 0xc9ea4 M')
        /\ (forall x, In x KS_atdZB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824296
        /\ getr R' (reg 10) = Z_to_bv 64 (V 13%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_278 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdZC := BndP_Na_012.LibSegNa_atdZC.
Definition KS_atdZC : list nat := Eval vm_compute in (BG.kept_list 80 PatdZC.regs0 PatdZC.regs_out0).
Lemma KS_atdZC_ok : BG.kept_ok 80 PatdZC.regs0 PatdZC.regs_out0 KS_atdZC = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_279 ())). Qed.
Lemma atdZC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 32 ->
  L5.u8_at RSEGS M ((V 50%nat) + 32) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc93e8 M) (st fx' R' 0xc9538 M')
        /\ (forall x, In x KS_atdZC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_280 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdD0 := BndP_Na_011.LibSegNa_atdD0.
Definition KS_atdD0_0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdD0.regs0 PatdD0.regs_out0).
Lemma KS_atdD0_0_ok : BG.kept_ok 80 PatdD0.regs0 PatdD0.regs_out0 KS_atdD0_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_281 ())). Qed.
Definition KS_atdD0_1 : list nat := Eval vm_compute in (BG.kept_list 80 PatdD0.regs0 PatdD0.regs_out1).
Lemma KS_atdD0_1_ok : BG.kept_ok 80 PatdD0.regs0 PatdD0.regs_out1 KS_atdD0_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_282 ())). Qed.
Lemma atdD0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 48 -> getr R (reg 13) = Z_to_bv 64 (V 37%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 4096 <= (V 36%nat) <= 140737488355327 ->
  1 <= (((V 10%nat) + (V 11%nat)) - (V 36%nat)) <= 31 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xc93a4 M) (st fx' R' 0xc9440 M')
        /\ (forall x, In x KS_atdD0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 10
        /\ getr R' (reg 25) = Z_to_bv 64 1
        /\ (V 11%nat) < 10)
      \/ (msteps RSEGS (st fx R 0xc93a4 M) (st fx' R' 0xc9428 M')
        /\ (forall x, In x KS_atdD0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 10
        /\ 10 <= (V 11%nat))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_283 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdD1 := BndP_Na_011.LibSegNa_atdD1.
Definition KS_atdD1 : list nat := Eval vm_compute in (BG.kept_list 80 PatdD1.regs0 PatdD1.regs_out0).
Lemma KS_atdD1_ok : BG.kept_ok 80 PatdD1.regs0 PatdD1.regs_out0 KS_atdD1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_284 ())). Qed.
Lemma atdD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 (V 40%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 32 ->
  1 <= (V 40%nat) <= 2 -> L5.writable RSEGS M ((V 2%nat) - 152) 8 -> L5.writable RSEGS M ((V 50%nat) + 96) 32 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 50%nat) + 96) <= bv_unsigned a < ((V 50%nat) + 96) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 50%nat) + 96) <= i < ((V 50%nat) + 96) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9440 M) (st fx' R' 0x7f058 M')
        /\ (forall x, In x KS_atdD1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824424
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 104)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 24
        /\ L5.u8_at RSEGS M' ((V 50%nat) + 96) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 13%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_285 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdD2 := BndP_Na_011.LibSegNa_atdD2.
Definition KS_atdD2 : list nat := Eval vm_compute in (BG.kept_list 80 PatdD2.regs0 PatdD2.regs_out0).
Lemma KS_atdD2_ok : BG.kept_ok 80 PatdD2.regs0 PatdD2.regs_out0 KS_atdD2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_286 ())). Qed.
Lemma atdD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 (V 40%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 1 <= (V 40%nat) <= 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9468 M) (st fx' R' 0xca420 M')
        /\ (forall x, In x KS_atdD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824436
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 96)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_287 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdD3 := BndP_Na_011.LibSegNa_atdD3.
Definition KS_atdD3 : list nat := Eval vm_compute in (BG.kept_list 80 PatdD3.regs0 PatdD3.regs_out0).
Lemma KS_atdD3_ok : BG.kept_ok 80 PatdD3.regs0 PatdD3.regs_out0 KS_atdD3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_288 ())). Qed.
Lemma atdD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 13%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 10%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 11%nat) -> getr R (reg 25) = Z_to_bv 64 (V 40%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 1 <= (V 11%nat) <= 31 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9474 M) (st fx' R' 0xc9484 M')
        /\ (forall x, In x KS_atdD3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 9
        /\ bv_unsigned (getr R' (reg 20)) = (((V 11%nat) + (if (V 11%nat) <? 1 then 1 else 0)) mod 2 ^ 64)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 10%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_289 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdL1 := BndP_Na_011.LibSegNa_atdL1.
Definition KS_atdL1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdL1.regs0 PatdL1.regs_out0).
Lemma KS_atdL1_0_ok : BG.kept_ok 80 PatdL1.regs0 PatdL1.regs_out0 KS_atdL1_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_290 ())). Qed.
Definition KS_atdL1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PatdL1.regs0 PatdL1.regs_out1).
Lemma KS_atdL1_1_ok : BG.kept_ok 80 PatdL1.regs0 PatdL1.regs_out1 KS_atdL1_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_291 ())). Qed.
Lemma atdL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 0 <= (V 10%nat) <= 140737488355328 -> 0 <= (V 11%nat) <= 31 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 4096 <= (V 36%nat) <= 140737488355327 ->
  L5.u8_at RSEGS M (V 36%nat) (V 37%nat) -> 0 <= (V 37%nat) <= 255 -> 1 <= (V 38%nat) <= 31 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xc9494 M) (st fx' R' 0xc9800 M')
        /\ (forall x, In x KS_atdL1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824492
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 96)
        /\ getr R' (reg 11) = Z_to_bv 64 10
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ (((V 37%nat) + 18446744073709551568) mod 2 ^ 64) <= 9)
      \/ (msteps RSEGS (st fx R 0xc9494 M) (st fx' R' 0xc9500 M')
        /\ (forall x, In x KS_atdL1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 22
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 37%nat) - 48)
        /\ 9 < (((V 37%nat) + 18446744073709551568) mod 2 ^ 64))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_292 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdL2 := BndP_Na_011.LibSegNa_atdL2.
Definition KS_atdL2 : list nat := Eval vm_compute in (BG.kept_list 80 PatdL2.regs0 PatdL2.regs_out0).
Lemma KS_atdL2_ok : BG.kept_ok 80 PatdL2.regs0 PatdL2.regs_out0 KS_atdL2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_293 ())). Qed.
Lemma atdL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 37%nat) - 48) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 48 <= (V 37%nat) <= 57 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc94ac M) (st fx' R' 0xc99fc M')
        /\ (forall x, In x KS_atdL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824504
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 96)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 37%nat) - 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_294 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdL3 := BndP_Na_011.LibSegNa_atdL3.
Definition KS_atdL3_0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdL3.regs0 PatdL3.regs_out0).
Lemma KS_atdL3_0_ok : BG.kept_ok 80 PatdL3.regs0 PatdL3.regs_out0 KS_atdL3_0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_295 ())). Qed.
Definition KS_atdL3_1 : list nat := Eval vm_compute in (BG.kept_list 80 PatdL3.regs0 PatdL3.regs_out1).
Lemma KS_atdL3_1_ok : BG.kept_ok 80 PatdL3.regs0 PatdL3.regs_out1 KS_atdL3_1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_296 ())). Qed.
Lemma atdL3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 ((V 37%nat) - 48) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> 4096 <= (V 36%nat) <= 140737488355327 -> 1 <= (V 38%nat) <= 31 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xc94b8 M) (st fx' R' 0xc9484 M')
        /\ (forall x, In x KS_atdL3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 38%nat) - 1)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ 1 <= (((((V 38%nat) + 18446744073709551615) mod 2 ^ 64) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xc94b8 M) (st fx' R' 0xc94dc M')
        /\ (forall x, In x KS_atdL3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 38%nat) - 1)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ (((((V 38%nat) + 18446744073709551615) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_297 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdDNp := BndP_Na_011.LibSegNa_atdDNp.
Definition KS_atdDNp : list nat := Eval vm_compute in (BG.kept_list 80 PatdDNp.regs0 PatdDNp.regs_out0).
Lemma KS_atdDNp_ok : BG.kept_ok 80 PatdDNp.regs0 PatdDNp.regs_out0 KS_atdDNp = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_298 ())). Qed.
Lemma atdDNp_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 13%nat) -> 7036928 <= (V 13%nat) <= 140737488355296 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc94dc M) (st fx' R' 0xc9ea4 M')
        /\ (forall x, In x KS_atdDNp -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824572
        /\ getr R' (reg 10) = Z_to_bv 64 (V 13%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 96)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_299 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdDNn := BndP_Na_011.LibSegNa_atdDNn.
Definition KS_atdDNn : list nat := Eval vm_compute in (BG.kept_list 80 PatdDNn.regs0 PatdDNn.regs_out0).
Lemma KS_atdDNn_ok : BG.kept_ok 80 PatdDNn.regs0 PatdDNn.regs_out0 KS_atdDNn = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_300 ())). Qed.
Lemma atdDNn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 13%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + (V 11%nat)) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 36%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.u64_at RSEGS M ((V 2%nat) - 144) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 13%nat) -> 7036928 <= (V 13%nat) <= 140737488355296 ->
  L5.u8_at RSEGS M ((V 50%nat) + 96) (V 45%nat) -> 0 <= (V 45%nat) <= 255 -> L5.writable RSEGS M ((V 50%nat) + 96) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 96) <= bv_unsigned a < ((V 50%nat) + 96) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 96) <= i < ((V 50%nat) + 96) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc94dc M) (st fx' R' 0xc9ea4 M')
        /\ (forall x, In x KS_atdDNn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824572
        /\ getr R' (reg 10) = Z_to_bv 64 (V 13%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 96)
        /\ L5.u8_at RSEGS M' ((V 50%nat) + 96) (((Z.land (V 45%nat) 18446744073709551613) + 2) mod 2 ^ 64)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_301 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdTi := BndP_Na_012.LibSegNa_atdTi.
Definition KS_atdTi : list nat := Eval vm_compute in (BG.kept_list 80 PatdTi.regs0 PatdTi.regs_out0).
Lemma KS_atdTi_ok : BG.kept_ok 80 PatdTi.regs0 PatdTi.regs_out0 KS_atdTi = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_302 ())). Qed.
Lemma atdTi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 (V 46%nat) -> getr R (reg 20) = Z_to_bv 64 (V 47%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 44%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.u8_at RSEGS M ((V 50%nat) + 96) (V 45%nat) -> 0 <= (V 45%nat) <= 255 -> Z.testbit (V 45%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9500 M) (st fx' R' 0xc9520 M')
        /\ (forall x, In x KS_atdTi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_303 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdTd := BndP_Na_012.LibSegNa_atdTd.
Definition KS_atdTd : list nat := Eval vm_compute in (BG.kept_list 80 PatdTd.regs0 PatdTd.regs_out0).
Lemma KS_atdTd_ok : BG.kept_ok 80 PatdTd.regs0 PatdTd.regs_out0 KS_atdTd = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_304 ())). Qed.
Lemma atdTd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 (V 46%nat) -> getr R (reg 20) = Z_to_bv 64 (V 47%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 44%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.u8_at RSEGS M ((V 50%nat) + 96) (V 45%nat) -> 0 <= (V 45%nat) <= 255 -> Z.testbit (V 45%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355264 -> L5.u64_at RSEGS M ((V 50%nat) + 112) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9500 M) (st fx' R' 0xf1fc0 M')
        /\ (forall x, In x KS_atdTd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 824608
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 64).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_305 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdU := BndP_Na_012.LibSegNa_atdU.
Definition KS_atdU : list nat := Eval vm_compute in (BG.kept_list 80 PatdU.regs0 PatdU.regs_out0).
Lemma KS_atdU_ok : BG.kept_ok 80 PatdU.regs0 PatdU.regs_out0 KS_atdU = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_306 ())). Qed.
Lemma atdU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 9 -> getr R (reg 19) = Z_to_bv 64 (V 46%nat) -> getr R (reg 20) = Z_to_bv 64 (V 47%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 50%nat) + 96) -> getr R (reg 24) = Z_to_bv 64 (V 44%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> 7036928 <= (V 50%nat) <= 140737488355072 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) ->
  (((V 2%nat) - 160) + 176 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9520 M) (st fx' R' 0xc9538 M')
        /\ (forall x, In x KS_atdU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 248).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_307 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdX := BndP_Na_012.LibSegNa_atdX.
Definition KS_atdX : list nat := Eval vm_compute in (BG.kept_list 80 PatdX.regs0 PatdX.regs_out0).
Lemma KS_atdX_ok : BG.kept_ok 80 PatdX.regs0 PatdX.regs_out0 KS_atdX = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_308 ())). Qed.
Lemma atdX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 68%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 5) = Z_to_bv 64 (V 70%nat) -> getr R (reg 6) = Z_to_bv 64 (V 71%nat) -> getr R (reg 7) = Z_to_bv 64 (V 72%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 67%nat) -> getr R (reg 11) = Z_to_bv 64 (V 73%nat) -> getr R (reg 12) = Z_to_bv 64 (V 66%nat) -> getr R (reg 13) = Z_to_bv 64 (V 74%nat) -> getr R (reg 14) = Z_to_bv 64 (V 75%nat) -> getr R (reg 15) = Z_to_bv 64 (V 76%nat) -> getr R (reg 16) = Z_to_bv 64 (V 77%nat) -> getr R (reg 17) = Z_to_bv 64 (V 78%nat) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 46%nat) -> getr R (reg 20) = Z_to_bv 64 (V 47%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) -> getr R (reg 23) = Z_to_bv 64 (V 39%nat) -> getr R (reg 24) = Z_to_bv 64 (V 44%nat) -> getr R (reg 25) = Z_to_bv 64 (V 42%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 28) = Z_to_bv 64 (V 79%nat) -> getr R (reg 29) = Z_to_bv 64 (V 69%nat) -> getr R (reg 30) = Z_to_bv 64 (V 48%nat) -> getr R (reg 31) = Z_to_bv 64 (V 49%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 7036928 <= (V 50%nat) <= 140737488355072 ->
  aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 256 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 32 -> L5.writable RSEGS M (V 50%nat) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 248) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 52%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 52%nat) - 160)) -> ((((V 50%nat) / 8) + 2147450880) + 32 <= (V 51%nat) \/ (V 51%nat) + 1 <= (((V 50%nat) / 8) + 2147450880)) -> (((V 52%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 256 <= ((V 52%nat) - 160)) ->
  0 <= (V 46%nat) <= 140737488355328 -> 0 <= (V 47%nat) <= 22 -> 140735332487296 <= (V 52%nat) <= 140737488355328 -> aligned (V 52%nat) 16 ->
  L5.u64_at RSEGS M ((V 52%nat) - 8) (V 53%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 16) (V 54%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 24) (V 55%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 32) (V 56%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 40) (V 57%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 48) (V 58%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 56) (V 59%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 64) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 72) (V 61%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 80) (V 62%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 88) (V 63%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 96) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 104) (V 65%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 32) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9538 M) (st fx' R' 0xc966c M')
        /\ (forall x, In x KS_atdX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 65%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdP ()) [] (Mh_0206_blobs1.kr_b_309 ())). Qed.
(* [comment removed for export] *)

End PNAETBDP.

End PnAEncTobdP.
Module PnAEncTobdPA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAEncTobdPA () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA8KS_atdA0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA6PatdA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA;KS_atdA0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA9KS_atdA16C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA7PatdA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206<PnAEncTobdPA9PNAETBDPA<KS_atdA16_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNAETBDPA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_310 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_311 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_312 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_313 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_314 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_315 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_316 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_317 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_318 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_319 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_320 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_321 ())). Qed.
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
Module PatdA0 := BndP_Na_011.LibSegNa_atdA0.
Definition KS_atdA0 : list nat := Eval vm_compute in (BG.kept_list 80 PatdA0.regs0 PatdA0.regs_out0).
Lemma KS_atdA0_ok : BG.kept_ok 80 PatdA0.regs0 PatdA0.regs_out0 KS_atdA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_322 ())). Qed.
Lemma atdA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9210 M) (st fx' R' 0x64af0 M')
        /\ (forall x, In x KS_atdA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 823948
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 12)
        /\ getr R' (reg 20) = getr R (reg 13)
        /\ getr R' (reg 22) = getr R (reg 10)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_323 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatdA16 := BndP_Na_011.LibSegNa_atdA16.
Definition KS_atdA16 : list nat := Eval vm_compute in (BG.kept_list 80 PatdA16.regs0 PatdA16.regs_out0).
Lemma KS_atdA16_ok : BG.kept_ok 80 PatdA16.regs0 PatdA16.regs_out0 KS_atdA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_324 ())). Qed.
Lemma atdA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 176) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 176) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc9210 M) (st fx' R' 0x64af0 M')
        /\ (forall x, In x KS_atdA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 823948
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 12)
        /\ getr R' (reg 20) = getr R (reg 13)
        /\ getr R' (reg 22) = getr R (reg 10)
        /\ getr R' (reg 24) = getr R (reg 11)
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAEncTobdPA ()) [] (Mh_0206_blobs1.kr_b_325 ())). Qed.
(* [comment removed for export] *)

End PNAETBDPA.

End PnAEncTobdPA.
Module PnATzP1.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0167.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnATzP1 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP18KS_atzA0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA0<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1=word_of_zpolyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA06cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA03kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzA03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1;KS_atzA0_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP19KS_atzA16C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17PatzA163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1<KS_atzA16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP17KS_atzBC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega=RingMicromega5Psatz07C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<kentry_KZeroC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1>u8_of_KWord1maC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega:ZMicromega;ZArithProof03c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP15PatzB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1:KS_atzB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP18KS_atzC0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP18KS_atzC1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzC13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP1;KS_atzC1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnATzP17PQATZP16PatzCm9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnATzP17PQATZP18KS_atzCmC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQATZP1.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_326 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_327 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_328 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_329 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_330 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_331 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_332 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_333 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_334 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_335 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_336 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_337 ())). Qed.
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
Module PatzA0 := BndP_Na_012.LibSegNa_atzA0.
Definition KS_atzA0 : list nat := Eval vm_compute in (BG.kept_list 80 PatzA0.regs0 PatzA0.regs_out0).
Lemma KS_atzA0_ok : BG.kept_ok 80 PatzA0.regs0 PatzA0.regs_out0 KS_atzA0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_338 ())). Qed.
Lemma atzA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc7770 M) (st fx' R' 0x64960 M')
        /\ (forall x, In x KS_atzA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 817108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_339 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatzA16 := BndP_Na_012.LibSegNa_atzA16.
Definition KS_atzA16 : list nat := Eval vm_compute in (BG.kept_list 80 PatzA16.regs0 PatzA16.regs_out0).
Lemma KS_atzA16_ok : BG.kept_ok 80 PatzA16.regs0 PatzA16.regs_out0 KS_atzA16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_340 ())). Qed.
Lemma atzA16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 16) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  L5.img_clear M 65536 1409024 -> L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> 140735332487264 <= (V 2%nat) <= 140737488355312 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 96) 112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc7770 M) (st fx' R' 0x64960 M')
        /\ (forall x, In x KS_atzA16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 817108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1440376
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' (V 2%nat) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_341 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatzB := BndP_Na_012.LibSegNa_atzB.
Definition KS_atzB : list nat := Eval vm_compute in (BG.kept_list 80 PatzB.regs0 PatzB.regs_out0).
Lemma KS_atzB_ok : BG.kept_ok 80 PatzB.regs0 PatzB.regs_out0 KS_atzB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_342 ())). Qed.
Lemma atzB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 80) 8 -> (((V 2%nat) - 96) + 96 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 96)) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> ((V 33%nat) + 32 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M (V 50%nat) 24 -> L5.writable RSEGS M ((V 50%nat) + 32) 32 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 12 ->
  7036928 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 ->
  L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 96) + 112 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 96)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 1) -> ~ (((V 50%nat) + 40) <= bv_unsigned a < ((V 50%nat) + 40) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 1) -> ~ (((V 50%nat) + 40) <= i < ((V 50%nat) + 40) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc77d4 M) (st fx' R' 0xcc1d8 M')
        /\ (forall x, In x KS_atzB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 817312
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 817008
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 56) 0
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) 0
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 40) 0
        /\ L5.u8_at RSEGS M' ((V 50%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 817008
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 110188
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 50%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_343 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatzC0 := BndP_Na_012.LibSegNa_atzC0.
Definition KS_atzC0 : list nat := Eval vm_compute in (BG.kept_list 80 PatzC0.regs0 PatzC0.regs_out0).
Lemma KS_atzC0_ok : BG.kept_ok 80 PatzC0.regs0 PatzC0.regs_out0 KS_atzC0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_344 ())). Qed.
Lemma atzC0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> ((V 33%nat) + 32 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M (V 50%nat) 8 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  ((V 33%nat) + 32 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> 140735332487264 <= (V 52%nat) <= 140737488355328 -> aligned (V 52%nat) 16 -> L5.u64_at RSEGS M ((V 52%nat) - 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 16) (V 54%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 24) (V 55%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 32) (V 56%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 40) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 48) (V 58%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 56) (V 59%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 64) (V 60%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 72) (V 61%nat) ->
  (((V 52%nat) - 96) + 96 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 52%nat) - 96)) -> (((V 52%nat) - 96) + 96 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 52%nat) - 96)) -> (((V 52%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 52%nat) - 96)) -> L5.u8_at RSEGS M ((V 50%nat) + 32) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc78a0 M) (st fx' R' 0xc7998 M')
        /\ (forall x, In x KS_atzC0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 61%nat)
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
ltac2:(KReplay.run1 (kr_tL_Mh_0206 ()) [] (Mh_0206_blobs1.kr_b_345 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatzC1 := BndP_Na_012.LibSegNa_atzC1.
Definition KS_atzC1 : list nat := Eval vm_compute in (BG.kept_list 80 PatzC1.regs0 PatzC1.regs_out0).
Lemma KS_atzC1_ok : BG.kept_ok 80 PatzC1.regs0 PatzC1.regs_out0 KS_atzC1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_346 ())). Qed.
Lemma atzC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> ((V 33%nat) + 32 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M (V 50%nat) 8 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  ((V 33%nat) + 32 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> 140735332487264 <= (V 52%nat) <= 140737488355328 -> aligned (V 52%nat) 16 -> L5.u64_at RSEGS M ((V 52%nat) - 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 16) (V 54%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 24) (V 55%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 32) (V 56%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 40) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 48) (V 58%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 56) (V 59%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 64) (V 60%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 72) (V 61%nat) ->
  (((V 52%nat) - 96) + 96 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 52%nat) - 96)) -> (((V 52%nat) - 96) + 96 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 52%nat) - 96)) -> (((V 52%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 52%nat) - 96)) -> L5.u8_at RSEGS M ((V 50%nat) + 32) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc78a0 M) (st fx' R' 0xc7998 M')
        /\ (forall x, In x KS_atzC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 61%nat)
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
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_347 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PatzCm := BndP_Na_012.LibSegNa_atzCm.
Definition KS_atzCm : list nat := Eval vm_compute in (BG.kept_list 80 PatzCm.regs0 PatzCm.regs_out0).
Lemma KS_atzCm_ok : BG.kept_ok 80 PatzCm.regs0 PatzCm.regs_out0 KS_atzCm = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnATzP1 ()) [] (Mh_0206_blobs1.kr_b_348 ())). Qed.
Lemma atzCm_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 10) = Z_to_bv 64 18446744073709551615 -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 50%nat) ->
  7036928 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> ((V 33%nat) + 32 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M (V 50%nat) 8 -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  ((V 33%nat) + 32 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> 140735332487264 <= (V 52%nat) <= 140737488355328 -> aligned (V 52%nat) 16 -> L5.u64_at RSEGS M ((V 52%nat) - 8) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 16) (V 54%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 24) (V 55%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 32) (V 56%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 40) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 52%nat) - 48) (V 58%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 56) (V 59%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 64) (V 60%nat) -> L5.u64_at RSEGS M ((V 52%nat) - 72) (V 61%nat) ->
  (((V 52%nat) - 96) + 96 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 52%nat) - 96)) -> (((V 52%nat) - 96) + 96 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 52%nat) - 96)) -> (((V 52%nat) - 96) + 96 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 52%nat) - 96)) -> L5.u8_at RSEGS M ((V 50%nat) + 32) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc78a0 M) (st fx' R' 0xc7998 M')
        /\ (forall x, In x KS_atzCm -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 61%nat)
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
ltac2:(KReplay.run1 (kr_tL_Mh_0206 ()) [] (Mh_0206_blobs1.kr_b_349 ())). Qed.
(* [comment removed for export] *)

End PQATZP1.

End PnATzP1.
Module PnACxaP.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0215.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnACxaP () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA6zpolyAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zpolyA_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA@u8_of_KWord1_modC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA>zeros_of_KZeroC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP7KS_acxAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorc69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA:zpolyA_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA6cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA3kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP5PacxA3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP:KS_acxA_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA39regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP8KS_acxA3C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA3<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA36cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA33ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP;KS_acxA3_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA59regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP8KS_acxA5C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA5<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA56cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP6PacxA53ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_02067PnACxaP6PMACXP;KS_acxA5_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PMACXP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_350 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_351 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_352 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_353 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_354 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_355 ())). Qed.
Lemma u8_of_KWord1ma E M b off e a v a' v' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v' = v mod 256 -> L5.u8_at RSEGS M a' v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_356 ())). Qed.
Lemma zeros_of_KZeroa E M b off ne a n a' : kentry_ok RSEGS E M (KZero (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5KA.zeros_at M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_357 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_358 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_359 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_360 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_361 ())). Qed.
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
Module PacxA := BndP_Na_003.LibSegNa_acxA.
Definition KS_acxA : list nat := Eval vm_compute in (BG.kept_list 48 PacxA.regs0 PacxA.regs_out0).
Lemma KS_acxA_ok : BG.kept_ok 48 PacxA.regs0 PacxA.regs_out0 KS_acxA = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_362 ())). Qed.
Lemma acxA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 4) = Z_to_bv 64 6896384 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) ->
  140735332488192 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 1024) 1024 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> L5.u32_at RSEGS M 6896400 (V 35%nat) -> 0 <= (V 35%nat) <= 2147483646 ->
  L5.writable RSEGS M 6896400 4 -> L5.u8_at RSEGS M 1443672 1 -> L5.u64_at RSEGS M 1412424 1276648 -> L5.u8_at RSEGS M 7027536 0 ->
  L5.u32_at RSEGS M 7027540 0 -> L5.u32_at RSEGS M 7027544 2 -> L5.u64_at RSEGS M 7027552 7027560 -> L5.writable RSEGS M 7027536 544 ->
  L5.u8_at RSEGS M 7028115 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 1024) <= bv_unsigned a < ((V 2%nat) - 1024) + 1024) -> ~ ((0 + 6896400) <= bv_unsigned a < (0 + 6896400) + 4) -> ~ ((0 + 7027544) <= bv_unsigned a < (0 + 7027544) + 4) -> ~ ((0 + 7027584) <= bv_unsigned a < (0 + 7027584) + 16) -> ~ ((0 + 7027840) <= bv_unsigned a < (0 + 7027840) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 1024) <= i < ((V 2%nat) - 1024) + 1024) -> ~ ((0 + 6896400) <= i < (0 + 6896400) + 4) -> ~ ((0 + 7027544) <= i < (0 + 7027544) + 4) -> ~ ((0 + 7027584) <= i < (0 + 7027584) + 16) -> ~ ((0 + 7027840) <= i < (0 + 7027840) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x74940 M) (st fx' R' 0x749c0 M')
        /\ (forall x, In x KS_acxA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 24
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' 6896400 (V 35%nat)
        /\ L5.u32_at RSEGS M' 7027544 4
        /\ L5.u64_at RSEGS M' 7027848 0
        /\ L5.u64_at RSEGS M' 7027592 477636
        /\ L5.u64_at RSEGS M' 7027840 (V 34%nat)
        /\ L5.u64_at RSEGS M' 7027584 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_363 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacxA3 := BndP_Na_003.LibSegNa_acxA3.
Definition KS_acxA3 : list nat := Eval vm_compute in (BG.kept_list 48 PacxA3.regs0 PacxA3.regs_out0).
Lemma KS_acxA3_ok : BG.kept_ok 48 PacxA3.regs0 PacxA3.regs_out0 KS_acxA3 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_364 ())). Qed.
Lemma acxA3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 4) = Z_to_bv 64 6896384 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) ->
  140735332488192 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 1024) 1024 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> L5.u32_at RSEGS M 6896400 (V 35%nat) -> 0 <= (V 35%nat) <= 2147483646 ->
  L5.writable RSEGS M 6896400 4 -> L5.u8_at RSEGS M 1443672 1 -> L5.u64_at RSEGS M 1412424 1276648 -> L5.u8_at RSEGS M 7027536 0 ->
  L5.u32_at RSEGS M 7027540 0 -> L5.u32_at RSEGS M 7027544 4 -> L5.u64_at RSEGS M 7027552 7027560 -> L5.writable RSEGS M 7027536 544 ->
  L5.u8_at RSEGS M 7028115 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 1024) <= bv_unsigned a < ((V 2%nat) - 1024) + 1024) -> ~ ((0 + 6896400) <= bv_unsigned a < (0 + 6896400) + 4) -> ~ ((0 + 7027544) <= bv_unsigned a < (0 + 7027544) + 4) -> ~ ((0 + 7027600) <= bv_unsigned a < (0 + 7027600) + 16) -> ~ ((0 + 7027856) <= bv_unsigned a < (0 + 7027856) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 1024) <= i < ((V 2%nat) - 1024) + 1024) -> ~ ((0 + 6896400) <= i < (0 + 6896400) + 4) -> ~ ((0 + 7027544) <= i < (0 + 7027544) + 4) -> ~ ((0 + 7027600) <= i < (0 + 7027600) + 16) -> ~ ((0 + 7027856) <= i < (0 + 7027856) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x74940 M) (st fx' R' 0x749c0 M')
        /\ (forall x, In x KS_acxA3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 40
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' 6896400 (V 35%nat)
        /\ L5.u32_at RSEGS M' 7027544 6
        /\ L5.u64_at RSEGS M' 7027864 0
        /\ L5.u64_at RSEGS M' 7027608 477636
        /\ L5.u64_at RSEGS M' 7027856 (V 34%nat)
        /\ L5.u64_at RSEGS M' 7027600 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_365 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacxA5 := BndP_Na_003.LibSegNa_acxA5.
Definition KS_acxA5 : list nat := Eval vm_compute in (BG.kept_list 48 PacxA5.regs0 PacxA5.regs_out0).
Lemma KS_acxA5_ok : BG.kept_ok 48 PacxA5.regs0 PacxA5.regs_out0 KS_acxA5 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_366 ())). Qed.
Lemma acxA5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 4) = Z_to_bv 64 6896384 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) ->
  140735332488192 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 1024) 1024 -> L5.img_clear M 1376256 1409024 ->
  L5.u64_at RSEGS M 1440376 2147450880 -> L5.u32_at RSEGS M 1440384 1 -> L5.u32_at RSEGS M 6896400 (V 35%nat) -> 0 <= (V 35%nat) <= 2147483646 ->
  L5.writable RSEGS M 6896400 4 -> L5.u8_at RSEGS M 1443672 1 -> L5.u64_at RSEGS M 1412424 1276648 -> L5.u8_at RSEGS M 7027536 0 ->
  L5.u32_at RSEGS M 7027540 0 -> L5.u32_at RSEGS M 7027544 6 -> L5.u64_at RSEGS M 7027552 7027560 -> L5.writable RSEGS M 7027536 544 ->
  L5.u8_at RSEGS M 7028115 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 1024) <= bv_unsigned a < ((V 2%nat) - 1024) + 1024) -> ~ ((0 + 6896400) <= bv_unsigned a < (0 + 6896400) + 4) -> ~ ((0 + 7027544) <= bv_unsigned a < (0 + 7027544) + 4) -> ~ ((0 + 7027616) <= bv_unsigned a < (0 + 7027616) + 16) -> ~ ((0 + 7027872) <= bv_unsigned a < (0 + 7027872) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 1024) <= i < ((V 2%nat) - 1024) + 1024) -> ~ ((0 + 6896400) <= i < (0 + 6896400) + 4) -> ~ ((0 + 7027544) <= i < (0 + 7027544) + 4) -> ~ ((0 + 7027616) <= i < (0 + 7027616) + 16) -> ~ ((0 + 7027872) <= i < (0 + 7027872) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x74940 M) (st fx' R' 0x749c0 M')
        /\ (forall x, In x KS_acxA5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 56
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' 6896400 (V 35%nat)
        /\ L5.u32_at RSEGS M' 7027544 8
        /\ L5.u64_at RSEGS M' 7027880 0
        /\ L5.u64_at RSEGS M' 7027624 477636
        /\ L5.u64_at RSEGS M' 7027872 (V 34%nat)
        /\ L5.u64_at RSEGS M' 7027616 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxaP ()) [] (Mh_0206_blobs1.kr_b_367 ())). Qed.
(* [comment removed for export] *)

End PMACXP.

End PnACxaP.
Module PnACxa.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.L5LazyA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsAX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0206.PnACxaP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0012.Na0_code_r6cfa8_6cfac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnACxa () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith4Znat5Z2Nat2idC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic3and00C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_wsegC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_00368AsanAcct<segs_below_bC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indK46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib7Mh_00368AsanAcctHfind_segment1_none_aboveC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c69OSSVerify5KrLib7Mh_02066PnACxa6PMACXA;segs_belowAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr04C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC59OSSVerify5KrLib7Mh_00387SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02107L5CoreA4L5CA9amodel_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5hl_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8hl_rt_roC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8model_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9aior_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SAR8vis_packC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A4avisC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ?lazy_cover_ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZHmrestrict_of_munrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ8sbm_lazyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ:sbm_vmmapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA5ly_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;art_privateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7aclientC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<block_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?aclientw_clientC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_02108L5StepAR5L5SARDaclientw_not_bshadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7cell_isC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:u32_at_visC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7hl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A8aly_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ:sbm_haltedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ<sbm_model_rtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZ8sbm_ahidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZCmunrestrict_visibleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00927L5LazyA4L5LZBcps_of_msteps_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8aclientwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A9wx_nowrapC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ7aior_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7ff_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ff_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9ff_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01797L5DefsA3L5A:aly_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<hl_rt_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9in_fframeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_02139PnSpecsAa3PMA=ly_ctr_staticC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z6moduloC47Corelib5Lists7ListDef3mapK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesC47Corelib4Init5Peano2ltI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_app1C46Stdlib5Lists4List>nth_error_app2C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ<atexit_cellsC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_max". Local Ltac lia := L5FastLia.plia.
Module PMACXA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) [] (Mh_0206_blobs1.kr_b_368 ())). Qed.
Lemma segs_belowA : segs_below_b RSEGS 0x6b6000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) [] (Mh_0206_blobs1.kr_b_369 ())). Qed.
(* [comment removed for export] *)
Lemma store_ok_defined (Mx : word -> option byte) a : 0x6b6000 <= a < 2 ^ 64 ->
  store_ok RSEGS Mx (Z_to_bv 64 a) 1 = true -> Mx (Z_to_bv 64 a) <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) [] (Mh_0206_blobs1.kr_b_370 ())). Qed.
Lemma u64_norm M a v : L5.u64_at RSEGS M a (bv_unsigned (Z_to_bv 64 v)) -> L5.u64_at RSEGS M a v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) [] (Mh_0206_blobs1.kr_b_371 ())). Qed.
(* [comment removed for export] *)
Lemma ret_rok fx R M (pc : Z) (W : bv 32) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  Hoare.ret_ok (getr R (reg 1)) ->
  msteps RSEGS (st fx R pc M) (st fx R (bv_unsigned (getr R (reg 1))) M).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) [] (Mh_0206_blobs1.kr_b_372 ())). Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis FCTR : HAJ.rt_frame_ctr L ar HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma apiece_ctr LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (W : Z -> Prop) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> L5CA.amodel_ok A model ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> W a -> ~ (hl_tp L + 16 <= a < hl_tp L + 20) -> aclientw L ar LB FF 0 0 a /\ ~ hl_rt_ro L a) ->
  L5.u32_at RSEGS M1v (hl_tp L + 16) 0 ->
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> L5CA.amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid A model a = false -> M1 a = M1v a) ->
      srealizes RSEGS SCFG (L5A.cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (L5A.cfg (fx:=fx) R pc M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) ["WithHeap"] (Mh_0206_blobs1.kr_b_373 ())). Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ctr_not_client LB FF LK cr A M V sp scr x :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar -> 0x693b10 <= x < 0x693b14 -> ~ aclient L ar LB FF sp scr x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) ["WithHeap"] (Mh_0206_blobs1.kr_b_374 ())). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma cells_snoc M X f0 a0 f1 a1 atc hs f a :     (* [comment removed for export] *)
  L5.u8_at RSEGS M X 0 -> L5.u32_at RSEGS M (X + 4) 0 -> L5.u32_at RSEGS M (X + 8) (4 + 2 * Z.of_nat (length hs)) ->
  L5.u64_at RSEGS M (X + 16) (X + 24) -> L5.u64_at RSEGS M (X + 24) 0 -> L5.u64_at RSEGS M (X + 32) f0 -> L5.u64_at RSEGS M (X + 288) a0 ->
  L5.u64_at RSEGS M (X + 40) f1 -> L5.u64_at RSEGS M (X + 296) a1 ->
  (forall (i : nat) fi ai, nth_error hs i = Some (fi, ai) ->
      L5.u64_at RSEGS M (X + 48 + 16 * Z.of_nat i) fi /\ L5.u64_at RSEGS M (X + 56 + 16 * Z.of_nat i) atc
      /\ L5.u64_at RSEGS M (X + 304 + 16 * Z.of_nat i) ai /\ L5.u64_at RSEGS M (X + 312 + 16 * Z.of_nat i) 0) ->
  (L5.u64_at RSEGS M (X + 48 + 16 * Z.of_nat (length hs)) f /\ L5.u64_at RSEGS M (X + 56 + 16 * Z.of_nat (length hs)) atc
   /\ L5.u64_at RSEGS M (X + 304 + 16 * Z.of_nat (length hs)) a /\ L5.u64_at RSEGS M (X + 312 + 16 * Z.of_nat (length hs)) 0) ->
  HAJ.atexit_cells RSEGS M X f0 a0 f1 a1 atc (hs ++ [(f, a)]).
Proof.
ltac2:(KReplay.run1 (kr_t_PnACxa ()) ["WithHeap"] (Mh_0206_blobs1.kr_b_375 ())). Qed.

Theorem cxa_atexit_ok : HAJ.cxa_atexit_spec L ar SCFG HI (HAJ.ec_cxa_pc PMA.EXT) (HAJ.ec_cxa_scr PMA.EXT) (HAJ.ec_atexit PMA.EXT)
                          (HAJ.ec_f0 PMA.EXT) (HAJ.ec_a0 PMA.EXT) (HAJ.ec_f1 PMA.EXT) (HAJ.ec_a1 PMA.EXT) (HAJ.ec_atc PMA.EXT) (HAJ.ec_nl PMA.EXT).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0206 ()) ["WithHeap"] (Mh_0206_blobs1.kr_b_376 ())). Qed.
End WithHeap.

End PMACXA.

End PnACxa.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8.
Module PnAHarnessKit4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnQStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PgV8. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5CoreA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0210.L5StepAR OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PmLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PmStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnStaticsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmModelFactsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PgV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnBrObjA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnStepA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.PnModelA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnRunA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnAKObj OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0256.PnAHarnessKit2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAHarnessKit4 () := "C47Corelib7Classes?RelationClasses9ReflexiveC46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_0089:HeapIfaceA3vmlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_okI35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00C69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>nth_error_pairC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_0256=PnAHarnessKit5PQHAK9blk_factsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_HIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA;mparser_ownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout<pa_vp_parserC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:mparser_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256=PnAHarnessKit5PQHAK9agA_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK47blk_rngC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA3agAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO=mparser_keepSC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4mpst00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5PSIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00249PnLayoutA6ADDR_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02138PmSpecsA5PMSPA4accAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4annAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA4aownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02137PnAKObj5PQAKO=adaptor_keepSC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00928PnModelA4PQMA3ast00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00928PnModelA4PQMA5ASIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0024:PnLayoutQA7QADDR_AC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib7Mh_02136PnRunA4PQRA4mownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK45hpar4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256>PnAHarnessKit26PQHAK22hfC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init5Logic2or01c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK4Bmparser_keep_pieceC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK4Badaptor_keep_pieceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256>PnAHarnessKit26PQHAK27u64_agAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA4agshC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C69OSSVerify5KrLib7Mh_0213=PmModelFactsA4PMFA:accA_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List2hdc69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK44hec4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA;shadow_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0256>PnAHarnessKit26PQHAK27u32_agAC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_0256>PnAHarnessKit26PQHAK27shz_agAC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib7Mh_0256>PnAHarnessKit26PQHAK26wapartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK48blk_rngcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK4Cmparser_keep_calleeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0206>PnAHarnessKit46PQHAK4Cadaptor_keep_calleeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQHAK4.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation mparser_at := (PQMA.mparser_at RSEGS PMA.AD PMSPA.accA PQRA.annA (pa_vp_parser PMA.AD)).
Abbreviation adaptor_at := (PQMA.adaptor_at RSEGS PMA.AD PMSPA.accA PQRA.annA (qa_vp_adaptor PnLayoutQA.QADDR_A)).

(* [comment removed for export] *)
Definition hpar4 (F : Z) (M : word -> option byte) (s : PQMA.mpst) (st : PQMA.ast) : Prop :=
  mparser_at M (F + 592) (F + 96) s /\ adaptor_at M (F + 992) (F + 496) st /\ L5.u64_at RSEGS M (F + 1088) (F + 992) /\ PMSPA.accA M (F + 592) 504.
(* [comment removed for export] *)
Definition hec4 (F : Z) (M : word -> option byte) (v c : Z) : Prop :=
  L5.u32_at RSEGS M (F + 1232) v /\ L5.u64_at RSEGS M (F + 1240) c /\ shadow_zero M (F + 1232) 2 /\ L5.defined M (F + 1232) 16.

Section K.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C scfg HI.

Section Objs.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : PQHAK2.hf F.
Variables (slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte).
Hypothesis S1 : ahl_ceil ar <= slo.
Hypothesis S2 : BIGSHADOW_HI <= slo.
Hypothesis FR : forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Hypothesis WP : PQHAK2.pfoot F slo shi Wp.
Let oav := PQHAK2.oav Wp.
Let BP := fun p c (Hin : In (p, c) LBx) => PQHAK2.blk_piece L ar C scfg HI HIok LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH Hin HF HFF S1 S2 FR WP.

Lemma blk_rng p c : In (p, c) LBx -> 0 <= p /\ p + c <= 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "Objs"] (Mh_0206_blobs1.kr_b_377 ())). Qed.

Lemma mparser_keep_piece op ois s : incl (PQMA.mparser_own s) LBx -> 0 <= op -> op + PQMA.PSIZE <= 2 ^ 47 -> oav op PQMA.PSIZE ->
  mparser_at M1 op ois s -> mparser_at M2 op ois s.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "Objs"] (Mh_0206_blobs1.kr_b_378 ())). Qed.
Lemma adaptor_keep_piece oa ov st : incl (PQMA.aown st) LBx -> 0 <= oa -> oa + PQMA.ASIZE <= 2 ^ 47 -> oav oa PQMA.ASIZE ->
  adaptor_at M1 oa ov st -> adaptor_at M2 oa ov st.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "Objs"] (Mh_0206_blobs1.kr_b_379 ())). Qed.
Lemma hpar4_piece s st : incl (PQRA.mown s st) LBx -> oav (F + 592) 504 -> hpar4 F M1 s st -> hpar4 F M2 s st.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "Objs"] (Mh_0206_blobs1.kr_b_380 ())). Qed.
Lemma hec4_piece v c : oav (F + 1232) 16 -> hec4 F M1 v c -> hec4 F M2 v c.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "Objs"] (Mh_0206_blobs1.kr_b_381 ())). Qed.
End Objs.

Section ObjsC.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : PQHAK2.hf F.
Variables (LBc : list (Z * Z)) (FFc : list fframe) (spc scrc : Z) (Wc : list L5.range) (M1 M2 : word -> option byte) (f : fframe).
Hypothesis AH : L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2.
Hypothesis WF : PQHAK2.wfi F Wc.
Hypothesis Hf : In f FFc.
Hypothesis HfF : ff_addr f = F /\ ff_bytes (ff_class f) = 2048.
Let BC := fun p c (Hin : In (p, c) LBx) (Hc : In (p, c) LBc) => PQHAK2.blk_callee L ar C scfg HI LY HIok LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2 HH Hin HF HFF AH Hc WF.
Let ffc := PQHAK2.ffc L ar F HFF LBc FFc spc scrc Wc M1 M2 f AH WF Hf HfF.

Lemma blk_rngc p c : In (p, c) LBx -> 0 <= p /\ p + c <= 2 ^ 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "ObjsC"] (Mh_0206_blobs1.kr_b_382 ())). Qed.

Lemma mparser_keep_callee op ois s : incl (PQMA.mparser_own s) LBx -> incl (PQMA.mparser_own s) LBc -> F + 32 <= op -> op + PQMA.PSIZE <= F + 2040 ->
  PQHAK2.wapart Wc op PQMA.PSIZE -> mparser_at M1 op ois s -> mparser_at M2 op ois s.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "ObjsC"] (Mh_0206_blobs1.kr_b_383 ())). Qed.
Lemma adaptor_keep_callee oa ov st : incl (PQMA.aown st) LBx -> incl (PQMA.aown st) LBc -> F + 32 <= oa -> oa + PQMA.ASIZE <= F + 2040 ->
  PQHAK2.wapart Wc oa PQMA.ASIZE -> adaptor_at M1 oa ov st -> adaptor_at M2 oa ov st.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "ObjsC"] (Mh_0206_blobs1.kr_b_384 ())). Qed.
Lemma hpar4_callee s st : incl (PQRA.mown s st) LBx -> incl (PQRA.mown s st) LBc -> PQHAK2.wapart Wc (F + 592) 504 -> hpar4 F M1 s st -> hpar4 F M2 s st.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "ObjsC"] (Mh_0206_blobs1.kr_b_385 ())). Qed.
Lemma hec4_callee v c : PQHAK2.wapart Wc (F + 1232) 16 -> hec4 F M1 v c -> hec4 F M2 v c.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAHarnessKit4 ()) ["K"; "ObjsC"] (Mh_0206_blobs1.kr_b_386 ())). Qed.
End ObjsC.
End K.
End PQHAK4.

End PnAHarnessKit4.
