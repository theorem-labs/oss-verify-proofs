(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Mh_0192_blobs1.
(* [comment removed for export] *)
Set Warnings "-require-in-module".
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module PnAdSNlP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0158 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSNlP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA015regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA019regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA01<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA013PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA012F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA013NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA013kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA013ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlA01_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA115regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA119regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA11C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA11<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA113PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA112F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA113NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA113kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA113ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlA11_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA205regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA209regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA20C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA20<seg_sound_axC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA203PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA202F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA203NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA203kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA203ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlA20_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA206cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA215regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA219regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA21C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA21<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA213PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA212F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA213NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA213kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA213ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlA21_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlA216cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9KS_ad_nlCC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlC3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlC_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlEd2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd2<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlEd23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlEd2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk0LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=u8_of_KWord1aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlEk0L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk0SC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S<seg_sound_axC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?u8x2_of_KWord2aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S6cells0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk0S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlEk0S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk1LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlEk1L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk1SC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlEk1S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlEk1S_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlILLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlILL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlILSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlILS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlILS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlISLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlISL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlISSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlISS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlISS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9KS_ad_nlJC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7Pad_nlJ3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlJ_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKILLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlKILL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKILSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKILS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlKILS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKISLC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISL3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlKISL_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKISSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKISS3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlKISS_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlKbnC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbn3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlKbn_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlKbzC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlKbz3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlKbz_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKdL2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlKdL2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdL26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKdS2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP?KS_ad_nlKdS2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:Pad_nlKdS26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:KS_ad_nlR1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlR13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=KS_ad_nlR1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlV1nC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1n3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlV1n_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlV1zC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9Pad_nlV1z3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>KS_ad_nlV1z_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:KS_ad_nlV2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP8Pad_nlV23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=KS_ad_nlV2_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADNLP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_001 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_002 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_003 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_004 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_005 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_006 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_007 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_008 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_009 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_010 ())). Qed.
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
Module Pad_nlA01 := BndP_Ns_034.LibSegNs_ad_nlA01.
Definition KS_ad_nlA01 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlA01.regs0 Pad_nlA01.regs_out0).
Lemma KS_ad_nlA01_ok : BG.kept_ok 64 Pad_nlA01.regs0 Pad_nlA01.regs_out0 KS_ad_nlA01 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_011 ())). Qed.
Lemma ad_nlA01_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 0 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b648 M) (st fx' R' 0x3b690 M')
        /\ (forall x, In x KS_ad_nlA01 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_012 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlA11 := BndP_Ns_034.LibSegNs_ad_nlA11.
Definition KS_ad_nlA11 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlA11.regs0 Pad_nlA11.regs_out0).
Lemma KS_ad_nlA11_ok : BG.kept_ok 64 Pad_nlA11.regs0 Pad_nlA11.regs_out0 KS_ad_nlA11 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_013 ())). Qed.
Lemma ad_nlA11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b648 M) (st fx' R' 0x3b690 M')
        /\ (forall x, In x KS_ad_nlA11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_014 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlA20 := BndP_Ns_034.LibSegNs_ad_nlA20.
Definition KS_ad_nlA20 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlA20.regs0 Pad_nlA20.regs_out0).
Lemma KS_ad_nlA20_ok : BG.kept_ok 64 Pad_nlA20.regs0 Pad_nlA20.regs_out0 KS_ad_nlA20 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_015 ())). Qed.
Lemma ad_nlA20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b648 M) (st fx' R' 0x3b690 M')
        /\ (forall x, In x KS_ad_nlA20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_016 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlA21 := BndP_Ns_034.LibSegNs_ad_nlA21.
Definition KS_ad_nlA21 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlA21.regs0 Pad_nlA21.regs_out0).
Lemma KS_ad_nlA21_ok : BG.kept_ok 64 Pad_nlA21.regs0 Pad_nlA21.regs_out0 KS_ad_nlA21 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_017 ())). Qed.
Lemma ad_nlA21_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 44%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b648 M) (st fx' R' 0x3b690 M')
        /\ (forall x, In x KS_ad_nlA21 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_018 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlC := BndP_Ns_034.LibSegNs_ad_nlC.
Definition KS_ad_nlC : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlC.regs0 Pad_nlC.regs_out0).
Lemma KS_ad_nlC_ok : BG.kept_ok 64 Pad_nlC.regs0 Pad_nlC.regs_out0 KS_ad_nlC = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_019 ())). Qed.
Lemma ad_nlC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b63c M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_nlC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243272
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 58).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_020 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlEd2 := BndP_Ns_034.LibSegNs_ad_nlEd2.
Definition KS_ad_nlEd2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlEd2.regs0 Pad_nlEd2.regs_out0).
Lemma KS_ad_nlEd2_ok : BG.kept_ok 64 Pad_nlEd2.regs0 Pad_nlEd2.regs_out0 KS_ad_nlEd2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_021 ())). Qed.
Lemma ad_nlEd2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 37%nat) - 24)) -> (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> 140735332483136 <= (V 38%nat) <= 140737488355272 -> (((V 2%nat) - 64) + 64 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 38%nat) 785968 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> L5.img_clear M 65536 814272 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b424 M) (st fx' R' 0x40838 M')
        /\ (forall x, In x KS_ad_nlEd2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242988
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = getr R (reg 13)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 264248
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_022 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlEk0L := BndP_Ns_034.LibSegNs_ad_nlEk0L.
Definition KS_ad_nlEk0L : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlEk0L.regs0 Pad_nlEk0L.regs_out0).
Lemma KS_ad_nlEk0L_ok : BG.kept_ok 64 Pad_nlEk0L.regs0 Pad_nlEk0L.regs_out0 KS_ad_nlEk0L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_023 ())). Qed.
Lemma ad_nlEk0L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.img_clear M 65536 814272 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) -> 0 <= (V 46%nat) <= 255 -> Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) -> 0 <= (V 47%nat) <= 2147483648 -> 4096 <= (V 48%nat) <= 140737487306752 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 32) <= bv_unsigned a < ((V 36%nat) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 32) <= i < ((V 36%nat) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b424 M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_nlEk0L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242872
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = getr R (reg 13)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 69321
        /\ getr R' (reg 13) = Z_to_bv 64 69325
        /\ getr R' (reg 14) = Z_to_bv 64 4
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_024 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlEk0S := BndP_Ns_034.LibSegNs_ad_nlEk0S.
Definition KS_ad_nlEk0S : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlEk0S.regs0 Pad_nlEk0S.regs_out0).
Lemma KS_ad_nlEk0S_ok : BG.kept_ok 64 Pad_nlEk0S.regs0 Pad_nlEk0S.regs_out0 KS_ad_nlEk0S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_025 ())). Qed.
Lemma ad_nlEk0S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> L5.img_clear M 65536 814272 ->
  L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) -> 0 <= (V 45%nat) <= 22 -> 0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b424 M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_nlEk0S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242872
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = getr R (reg 13)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 12) = Z_to_bv 64 69321
        /\ getr R' (reg 13) = Z_to_bv 64 69325
        /\ getr R' (reg 14) = Z_to_bv 64 4
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ (L5.u8_at RSEGS M' ((V 36%nat) + 24) 0 /\ L5.u8_at RSEGS M' (((V 36%nat) + 24) + 1) 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_026 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlEk1L := BndP_Ns_034.LibSegNs_ad_nlEk1L.
Definition KS_ad_nlEk1L : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlEk1L.regs0 Pad_nlEk1L.regs_out0).
Lemma KS_ad_nlEk1L_ok : BG.kept_ok 64 Pad_nlEk1L.regs0 Pad_nlEk1L.regs_out0 KS_ad_nlEk1L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_027 ())). Qed.
Lemma ad_nlEk1L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.img_clear M 65536 814272 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) -> 0 <= (V 46%nat) <= 255 -> Z.testbit (V 46%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) -> 0 <= (V 47%nat) <= 2147483648 -> 4096 <= (V 48%nat) <= 140737487306752 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 32) <= bv_unsigned a < ((V 36%nat) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> ~ (((V 36%nat) + 32) <= i < ((V 36%nat) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b424 M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_nlEk1L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242872
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = getr R (reg 13)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 69321
        /\ getr R' (reg 13) = Z_to_bv 64 69325
        /\ getr R' (reg 14) = Z_to_bv 64 4
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_028 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlEk1S := BndP_Ns_035.LibSegNs_ad_nlEk1S.
Definition KS_ad_nlEk1S : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlEk1S.regs0 Pad_nlEk1S.regs_out0).
Lemma KS_ad_nlEk1S_ok : BG.kept_ok 64 Pad_nlEk1S.regs0 Pad_nlEk1S.regs_out0 KS_ad_nlEk1S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_029 ())). Qed.
Lemma ad_nlEk1S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.img_clear M 65536 814272 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) -> 0 <= (V 45%nat) <= 22 -> 0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> ~ (((V 36%nat) + 24) <= bv_unsigned a < ((V 36%nat) + 24) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> ~ (((V 36%nat) + 24) <= i < ((V 36%nat) + 24) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b424 M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_nlEk1S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242872
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = getr R (reg 13)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 12) = Z_to_bv 64 69321
        /\ getr R' (reg 13) = Z_to_bv 64 69325
        /\ getr R' (reg 14) = Z_to_bv 64 4
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = getr R (reg 11)
        /\ (L5.u8_at RSEGS M' ((V 36%nat) + 24) 0 /\ L5.u8_at RSEGS M' (((V 36%nat) + 24) + 1) 0)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_030 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlILL := BndP_Ns_035.LibSegNs_ad_nlILL.
Definition KS_ad_nlILL : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlILL.regs0 Pad_nlILL.regs_out0).
Lemma KS_ad_nlILL_ok : BG.kept_ok 64 Pad_nlILL.regs0 Pad_nlILL.regs_out0 KS_ad_nlILL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_031 ())). Qed.
Lemma ad_nlILL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 50%nat) ->
  0 <= (V 50%nat) <= 255 -> Z.testbit (V 50%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 52%nat) ->
  0 <= (V 51%nat) <= 2147483648 -> 4096 <= (V 52%nat) <= 140737487306752 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) -> 0 <= (V 46%nat) <= 255 ->
  Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) -> 0 <= (V 47%nat) <= 2147483648 ->
  4096 <= (V 48%nat) <= 140737487306752 -> L5.writable RSEGS M (V 48%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4f4 M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlILL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243136
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 51%nat) + (V 52%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 47%nat) + (V 48%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_032 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlILS := BndP_Ns_035.LibSegNs_ad_nlILS.
Definition KS_ad_nlILS : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlILS.regs0 Pad_nlILS.regs_out0).
Lemma KS_ad_nlILS_ok : BG.kept_ok 64 Pad_nlILS.regs0 Pad_nlILS.regs_out0 KS_ad_nlILS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_033 ())). Qed.
Lemma ad_nlILS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 50%nat) ->
  0 <= (V 50%nat) <= 255 -> Z.testbit (V 50%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 52%nat) ->
  0 <= (V 51%nat) <= 2147483648 -> 4096 <= (V 52%nat) <= 140737487306752 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) -> 0 <= (V 45%nat) <= 22 ->
  0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4f4 M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlILS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243136
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 51%nat) + (V 52%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 45%nat)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 45%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_034 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlISL := BndP_Ns_035.LibSegNs_ad_nlISL.
Definition KS_ad_nlISL : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlISL.regs0 Pad_nlISL.regs_out0).
Lemma KS_ad_nlISL_ok : BG.kept_ok 64 Pad_nlISL.regs0 Pad_nlISL.regs_out0 KS_ad_nlISL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_035 ())). Qed.
Lemma ad_nlISL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (2 * (V 49%nat)) ->
  0 <= (V 49%nat) <= 22 -> 0 <= (Z.land ((2 * (V 49%nat)) mod 2 ^ 64) 1) <= 0 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) -> 0 <= (V 46%nat) <= 255 ->
  Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) -> 0 <= (V 47%nat) <= 2147483648 ->
  4096 <= (V 48%nat) <= 140737487306752 -> L5.writable RSEGS M (V 48%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4f4 M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlISL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243136
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 49%nat)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 47%nat) + (V 48%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_036 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlISS := BndP_Ns_035.LibSegNs_ad_nlISS.
Definition KS_ad_nlISS : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlISS.regs0 Pad_nlISS.regs_out0).
Lemma KS_ad_nlISS_ok : BG.kept_ok 64 Pad_nlISS.regs0 Pad_nlISS.regs_out0 KS_ad_nlISS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_037 ())). Qed.
Lemma ad_nlISS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (2 * (V 49%nat)) ->
  0 <= (V 49%nat) <= 22 -> 0 <= (Z.land ((2 * (V 49%nat)) mod 2 ^ 64) 1) <= 0 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) -> 0 <= (V 45%nat) <= 22 ->
  0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4f4 M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlISS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243136
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 49%nat)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 45%nat)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 45%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_038 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlJ := BndP_Ns_035.LibSegNs_ad_nlJ.
Definition KS_ad_nlJ : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlJ.regs0 Pad_nlJ.regs_out0).
Lemma KS_ad_nlJ_ok : BG.kept_ok 64 Pad_nlJ.regs0 Pad_nlJ.regs_out0 KS_ad_nlJ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_039 ())). Qed.
Lemma ad_nlJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b5c0 M) (st fx' R' 0x3b648 M')
        /\ (forall x, In x KS_ad_nlJ -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_040 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKILL := BndP_Ns_035.LibSegNs_ad_nlKILL.
Definition KS_ad_nlKILL : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKILL.regs0 Pad_nlKILL.regs_out0).
Lemma KS_ad_nlKILL_ok : BG.kept_ok 64 Pad_nlKILL.regs0 Pad_nlKILL.regs_out0 KS_ad_nlKILL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_041 ())). Qed.
Lemma ad_nlKILL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 50%nat) ->
  0 <= (V 50%nat) <= 255 -> Z.testbit (V 50%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 52%nat) ->
  0 <= (V 51%nat) <= 2147483648 -> 4096 <= (V 52%nat) <= 140737487306752 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) -> 0 <= (V 46%nat) <= 255 ->
  Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) -> 0 <= (V 47%nat) <= 2147483648 ->
  4096 <= (V 48%nat) <= 140737487306752 -> L5.writable RSEGS M (V 48%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b54c M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlKILL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243260
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 51%nat) + (V 52%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 47%nat) + (V 48%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_042 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKILS := BndP_Ns_035.LibSegNs_ad_nlKILS.
Definition KS_ad_nlKILS : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKILS.regs0 Pad_nlKILS.regs_out0).
Lemma KS_ad_nlKILS_ok : BG.kept_ok 64 Pad_nlKILS.regs0 Pad_nlKILS.regs_out0 KS_ad_nlKILS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_043 ())). Qed.
Lemma ad_nlKILS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 50%nat) ->
  0 <= (V 50%nat) <= 255 -> Z.testbit (V 50%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 52%nat) ->
  0 <= (V 51%nat) <= 2147483648 -> 4096 <= (V 52%nat) <= 140737487306752 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) -> 0 <= (V 45%nat) <= 22 ->
  0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b54c M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlKILS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243260
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 51%nat) + (V 52%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 45%nat)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 45%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_044 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKISL := BndP_Ns_035.LibSegNs_ad_nlKISL.
Definition KS_ad_nlKISL : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKISL.regs0 Pad_nlKISL.regs_out0).
Lemma KS_ad_nlKISL_ok : BG.kept_ok 64 Pad_nlKISL.regs0 Pad_nlKISL.regs_out0 KS_ad_nlKISL = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_045 ())). Qed.
Lemma ad_nlKISL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (2 * (V 49%nat)) ->
  0 <= (V 49%nat) <= 22 -> 0 <= (Z.land ((2 * (V 49%nat)) mod 2 ^ 64) 1) <= 0 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) -> 0 <= (V 46%nat) <= 255 ->
  Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) -> 0 <= (V 47%nat) <= 2147483648 ->
  4096 <= (V 48%nat) <= 140737487306752 -> L5.writable RSEGS M (V 48%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b54c M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlKISL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243260
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 49%nat)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 47%nat) + (V 48%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 47%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_046 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKISS := BndP_Ns_035.LibSegNs_ad_nlKISS.
Definition KS_ad_nlKISS : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKISS.regs0 Pad_nlKISS.regs_out0).
Lemma KS_ad_nlKISS_ok : BG.kept_ok 64 Pad_nlKISS.regs0 Pad_nlKISS.regs_out0 KS_ad_nlKISS = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_047 ())). Qed.
Lemma ad_nlKISS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (2 * (V 49%nat)) ->
  0 <= (V 49%nat) <= 22 -> 0 <= (Z.land ((2 * (V 49%nat)) mod 2 ^ 64) 1) <= 0 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) -> 0 <= (V 45%nat) <= 22 ->
  0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b54c M) (st fx' R' 0x3ccec M')
        /\ (forall x, In x KS_ad_nlKISS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243260
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 49%nat)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 25)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 45%nat)) + 25)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 45%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_048 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKbn := BndP_Ns_035.LibSegNs_ad_nlKbn.
Definition KS_ad_nlKbn : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKbn.regs0 Pad_nlKbn.regs_out0).
Lemma KS_ad_nlKbn_ok : BG.kept_ok 64 Pad_nlKbn.regs0 Pad_nlKbn.regs_out0 KS_ad_nlKbn = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_049 ())). Qed.
Lemma ad_nlKbn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.u64_at RSEGS M ((V 37%nat) - 8) (V 39%nat) -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_nlKbn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 243020
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_050 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKbz := BndP_Ns_035.LibSegNs_ad_nlKbz.
Definition KS_ad_nlKbz : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKbz.regs0 Pad_nlKbz.regs_out0).
Lemma KS_ad_nlKbz_ok : BG.kept_ok 64 Pad_nlKbz.regs0 Pad_nlKbz.regs_out0 KS_ad_nlKbz = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_051 ())). Qed.
Lemma ad_nlKbz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x3b54c M')
        /\ (forall x, In x KS_ad_nlKbz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_052 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKdL2 := BndP_Ns_035.LibSegNs_ad_nlKdL2.
Definition KS_ad_nlKdL2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKdL2.regs0 Pad_nlKdL2.regs_out0).
Lemma KS_ad_nlKdL2_ok : BG.kept_ok 64 Pad_nlKdL2.regs0 Pad_nlKdL2.regs_out0 KS_ad_nlKdL2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_053 ())). Qed.
Lemma ad_nlKdL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 37%nat) - 24)) -> (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> 140735332483136 <= (V 38%nat) <= 140737488355272 -> (((V 2%nat) - 64) + 64 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 38%nat) 785968 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> L5.img_clear M 65536 814272 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (V 46%nat) ->
  0 <= (V 46%nat) <= 255 -> Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 40) (V 48%nat) ->
  0 <= (V 47%nat) <= 2147483648 -> 4096 <= (V 48%nat) <= 140737487306752 -> L5.writable RSEGS M (V 48%nat) 1 -> (((V 2%nat) - 64) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 64)) ->
  ((V 36%nat) + 96 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((V 48%nat) + 1 <= 65536 \/ 65536 + 958464 <= (V 48%nat)) -> ((V 48%nat) + 1 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 48%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 56) <= bv_unsigned a < ((V 2%nat) - 56) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 56) <= i < ((V 2%nat) - 56) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x40810 M')
        /\ (forall x, In x KS_ad_nlKdL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242988
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 12) = getr R (reg 18)
        /\ getr R' (reg 13) = getr R (reg 9)
        /\ getr R' (reg 14) = Z_to_bv 64 264208
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 48%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_054 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlKdS2 := BndP_Ns_035.LibSegNs_ad_nlKdS2.
Definition KS_ad_nlKdS2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlKdS2.regs0 Pad_nlKdS2.regs_out0).
Lemma KS_ad_nlKdS2_ok : BG.kept_ok 64 Pad_nlKdS2.regs0 Pad_nlKdS2.regs_out0 KS_ad_nlKdS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_055 ())). Qed.
Lemma ad_nlKdS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 37%nat) - 24)) -> (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> 140735332483136 <= (V 38%nat) <= 140737488355272 -> (((V 2%nat) - 64) + 64 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 38%nat) 785968 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> L5.img_clear M 65536 814272 -> L5.u8_at RSEGS M ((V 36%nat) + 24) (2 * (V 45%nat)) ->
  0 <= (V 45%nat) <= 22 -> 0 <= (Z.land ((2 * (V 45%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 56) <= bv_unsigned a < ((V 2%nat) - 56) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 56) <= i < ((V 2%nat) - 56) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x40810 M')
        /\ (forall x, In x KS_ad_nlKdS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242988
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 12) = getr R (reg 18)
        /\ getr R' (reg 13) = getr R (reg 9)
        /\ getr R' (reg 14) = Z_to_bv 64 264208
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 36%nat) + 25)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_056 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlR1 := BndP_Ns_036.LibSegNs_ad_nlR1.
Definition KS_ad_nlR1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlR1.regs0 Pad_nlR1.regs_out0).
Lemma KS_ad_nlR1_ok : BG.kept_ok 64 Pad_nlR1.regs0 Pad_nlR1.regs_out0 KS_ad_nlR1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_057 ())). Qed.
Lemma ad_nlR1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b52c M) (st fx' R' 0x3b648 M')
        /\ (forall x, In x KS_ad_nlR1 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_058 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlV1n := BndP_Ns_036.LibSegNs_ad_nlV1n.
Definition KS_ad_nlV1n : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlV1n.regs0 Pad_nlV1n.regs_out0).
Lemma KS_ad_nlV1n_ok : BG.kept_ok 64 Pad_nlV1n.regs0 Pad_nlV1n.regs_out0 KS_ad_nlV1n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_059 ())). Qed.
Lemma ad_nlV1n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) (V 39%nat) -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_nlV1n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 242932
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_060 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlV1z := BndP_Ns_036.LibSegNs_ad_nlV1z.
Definition KS_ad_nlV1z : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlV1z.regs0 Pad_nlV1z.regs_out0).
Lemma KS_ad_nlV1z_ok : BG.kept_ok 64 Pad_nlV1z.regs0 Pad_nlV1z.regs_out0 KS_ad_nlV1z = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_061 ())). Qed.
Lemma ad_nlV1z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x3b4f4 M')
        /\ (forall x, In x KS_ad_nlV1z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_062 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_nlV2 := BndP_Ns_036.LibSegNs_ad_nlV2.
Definition KS_ad_nlV2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_nlV2.regs0 Pad_nlV2.regs_out0).
Lemma KS_ad_nlV2_ok : BG.kept_ok 64 Pad_nlV2.regs0 Pad_nlV2.regs_out0 KS_ad_nlV2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_063 ())). Qed.
Lemma ad_nlV2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 64) + 64 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 64)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b4b8 M) (st fx' R' 0x3b4f4 M')
        /\ (forall x, In x KS_ad_nlV2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 2).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNlP ()) [] (Mh_0192_blobs1.kr_b_064 ())). Qed.
(* [comment removed for export] *)

End PQADNLP.

End PnAdSNlP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool Permutation FunctionalExtensionality. From stdpp Require base list. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdECall. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0252. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef Utf8Facts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0192 () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List7map_appC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_tC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_kC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_01028PnQModel3PQM5lv_eoC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00I46Stdlib9micromega5Tauto8GFormula00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01I46Stdlib9micromega7EnvRing3Pol00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3advC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_01028NemModel3NEM6ae_kbbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ndestC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega5Psatz07K69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lv_shapeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2cmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5aeownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_kbgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5savesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK5worldC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4xinvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6pot_aeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3G64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL8xinv_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK<lv_shape_advC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM;ndest_kindsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9adaptor_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL6own_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:in_block_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK8reg_backC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:cs_restoreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_01028NemModel3NEM3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3phiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6edepthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:pot_vstackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:pot_estackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lvec_ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlA20_concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlA21_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlA01_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF<u32_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlA11_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib5Lists7ListDef3mapK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3PMEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4LITNC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7e_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4c_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA20C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA21C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlA11C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM;pot_adaptorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4aownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL<pot_ae_splitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4ea_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ea_bsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:content_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_add_rC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL6cme_cmC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4prepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:aeown_appWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL6kc_frzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC:ascii_utf8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5zsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8cle_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<ad_nlR1_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:saves_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL;short_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlKdS2_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:long_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlKdL2_concC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ENC_HSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:KS_ad_nlR1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKdS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKdL2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9cm_of_cmeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9xinv_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5COLONC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5TOADVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlKISS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlISS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlKISL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlISL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlKILS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlILS_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlKILL_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlILL_concC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpK47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4CRa0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKISSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlISSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKISLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlISLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKILSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlILSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlKILLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlILLC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC69OSSVerify5KrLib7Mh_01428PnAdKit25PQAK2>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7KEYDESTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlKbz_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4INS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlKbn_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5COMMAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<ad_nlV2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlV1z_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlV1n_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlKbzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlKbnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:KS_ad_nlV2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlV1zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlV1nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4kclrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL8kclr_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6or_decC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8inW_hereC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib5Lists7ListDef3nthK47Corelib5Lists7ListDef6Forall01c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9kclr_sizeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL8kclr_ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9kclr_dataC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7kclr_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9kbc_keyopC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4DISPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlEk1S_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=defined_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlEk0S_concC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL8pk_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlEk1L_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP>ad_nlEk0L_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4AAa0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3LITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk1SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk0SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5xinv0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9aeown_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4LITBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9lit_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9lit_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk1LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<KS_ad_nlEk0LC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxc69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5kept0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5savesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4xinvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8xinv_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS6own_lvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:in_block_eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:cs_restoreC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3FINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsA20_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsA21_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsA01_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsA11_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9TAG_ENANOC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS7e_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4c_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA20C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA21C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA11C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3ENVC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z=mod_pos_boundc69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4prepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4ENVcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3EDKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<ad_vsKz_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4VIEWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3INSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3EPBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<ad_vsKn_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS2Q1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3EDVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<ad_vsV2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsV1z_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsV1n_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsKzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsKnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsV2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsV1zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsV1nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4AAa0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3cslC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symI47Corelib5Lists7ListDef6Forall00c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR8st_factsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT;ecap_nonnegC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_0_rC56Stdlib6ZArith6BinInt1Z7add_0_rc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brV0_concC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC56Stdlib5Arith8PeanoNat3Nat6eq_decC47Corelib4Init5Logic6or_indC69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3FINC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT8al8_itemC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0135:PmCertKitG4PMCG>u64_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brV1w_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brV1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4cinvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brV0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brV1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40edcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40edcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40edcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brV1wC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3COKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2gtK47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brF1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR6CSLsubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR7CSLcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR4at_TC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brF2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brF4_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brF8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brF16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE8a_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE8n_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE8b_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE8c_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE8d_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE8e_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brW16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brE32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brW32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8nC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brW16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brW32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brF16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8aC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8dC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3cslC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST8st_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9btV0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3FINC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btV1w_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9btV1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3CSLC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btV0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btV1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347W_40dc4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347F_40dc4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibDNs0_code_3fce0_410347D_40dc4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btV1wC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3COKC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9btH8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST6CSLsubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST7CSLcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btH8b_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST4at_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btH16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btW16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btH32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btW32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btH8bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btW16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btW32C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btH8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btH16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btH32C1?~~~~~~~~~~~~~~~".
Module PnAdSNl.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdECall. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0252. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnMpKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnMpBaKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSIns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdLvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnMpKitN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdECall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0252.PnAdFromU OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0192.PnAdSNlP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r3afcc_3afd0.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef Utf8Facts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSNl () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29img_bytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3LITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4LITNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4LITBC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_01028NemModel3NEM5asciiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib7Mh_01025PnVis3PQV4ndigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_01025PnVis3PQV6ndig_fC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib7Mh_02529PnAdFromU6PQADFU:ndig_f_ge1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z9pow_add_rC56Stdlib6ZArith6BinInt1Z7pow_1_rK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succC47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9ndig_f_lbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7ndig_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5w_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02529PnAdFromU6PQADFU9ndig_f_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4kclrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM;pot_adaptorC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:pot_estackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3PMEC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK<sink_pot_fstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK?sink_pot_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK6PME_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_01028NemModel3NEM5aeownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List4inclC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9aeown_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appK47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4BRXeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6pot_aeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL<pot_ae_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL>enc_pot_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9cle_add_rC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3ENKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5savesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lvec_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_atC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8pow2_posC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ndestC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_kbgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_lec69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4AAa0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ASIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lv_rootC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4HHe0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8app_nth2C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_tC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC56Stdlib5Arith8PeanoNat3Nat6eq_decC46Stdlib5Lists4ListClength_zero_iff_nilC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK:own_not_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2cmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9ek_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;client_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5kept0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6sub_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK8reg_backC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4xinvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib7Mh_00188PmLayout?pa_errcat_guardC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST9atexit_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP;clear_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP5sf_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST<atexit_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lvec_ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9blocks_hiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL8lv_apartC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;PermutationHPermutation_app_swap_appC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9heap_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnMpKitN4PNMK>kcontent_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT<enc_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT=sink_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT>ec_state_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:err_ok_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3phiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6edepthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r3afcc_3afd07W_3b648C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r3afcc_3afd07F_3b648C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r3afcc_3afd07D_3b648C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK7land2_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5lv_eoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7e_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9cm_of_cmeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4prepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP=ad_nlEd2_concC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL8xinv_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9adaptor_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK5worldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout7ne_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5pre_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6step_wC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z7add_modC59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8eargs_t3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP<ad_nlR1_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:saves_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL3ADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP:KS_ad_nlR1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;KS_ad_nlEd2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL5xinv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;ad_nlJ_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_add_rC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:aeown_appWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9KS_ad_nlJC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7dphi_geC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP;ad_nlC_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8cle_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7ascii_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL9xinv_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSNlP7PQADNLP9KS_ad_nlCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4CRa0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL7kc_kbopC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4INS2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL:long_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL6MAIN_KC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL6MAIN_DC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4c_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;exists_lastC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8args_ec3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV7pre_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8step_valC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00I47Corelib4Init6Specif4sigT00c69OSSVerify5KrLib7Mh_01927PnAdSNl6PNADNL4MAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ9qa_v_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV;v_null_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5zsizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01026PnVisN3PNV5VIS_HC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV6d_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNADNL.
Import PMS.
Import NEM.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation AQ := PnLayoutQS.QADDR_S.
Abbreviation AE := NemLayoutS.NEADDR_S.
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation adaptor_at := (PQM.adaptor_at RSEGS AD PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).
Abbreviation ec_state := (NEM.ec_state RSEGS AD).
Abbreviation err_ok := (PQST.err_ok RSEGS AD AQ).
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).
(* [comment removed for export] *)
Definition LIT : Z := 0x10ec9.
Definition LITN : Z := 4.
Definition LITB : list Z := [110; 117; 108; 108].
Lemma lit_bytes : AX2.img_bytes RSEGS LIT (Z.to_nat LITN) = Some LITB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_065 ())). Qed.
Lemma lit_ascii : ascii LITB.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_066 ())). Qed.

(* [comment removed for export] *)
Lemma ndig_eq v : PNV.ndig v = PQV.ndig v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_067 ())). Qed.
Lemma ndig_f_lb f : forall v k, 10 ^ k <= v -> k <= Z.of_nat f -> 0 <= k -> k + 1 <= PQV.ndig_f f v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_068 ())). Qed.
Lemma ndig_lb v k : 0 <= k <= 19 -> 10 ^ k <= v -> k + 1 <= PQV.ndig v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_069 ())). Qed.
Lemma w_u64_ndig v : 0 <= v -> w_u64 v <= PQV.ndig v + 2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_070 ())). Qed.
Lemma ndig_u32 v : 0 <= v < 2 ^ 32 -> PQV.ndig v <= 10.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) [] (Mh_0192_blobs1.kr_b_071 ())). Qed.
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
(* [comment removed for export] *)
Hypothesis VNE : NECS.v_null_spec RSEGS AD AQ AE L HI NESK.PME.
Hypothesis VKE : NECS.v_key_spec RSEGS AD AQ AE L HI NESK.PME.
Abbreviation ae_at := (NEM.ae_at RSEGS AD AE L PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).
Abbreviation enc_at := (NEM.enc_at RSEGS AE L PMSP.T3 PMSP.T4).
Abbreviation sink_at := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 NESK.PME).

(* [comment removed for export] *)
Definition kclr (x : PM.vstr) : PM.vstr := match x with PM.VShort _ => PM.VShort 0 | PM.VLong cc _ qq => PM.VLong cc 0 qq end.
Lemma kclr_size x : PM.vs_size (kclr x) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_072 ())). Qed.
Lemma kclr_data o x : PM.vs_data o (kclr x) = PM.vs_data o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_073 ())). Qed.
Lemma kclr_ok x g : PQM.ks_ok PQM.SMK x g -> PQM.ks_ok PQM.SMK (kclr x) g.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_074 ())). Qed.
Lemma kclr_pot lvX bX kX kx kgx kbx gx : PQM.pot_adaptor L (PQM.AST lvX bX kX (kclr kx) kgx kbx gx) = PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_075 ())). Qed.
Lemma kclr_own lvX bX kX kx kgx kbx gx : PQM.aown (PQM.AST lvX bX kX (kclr kx) kgx kbx gx) = PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_076 ())). Qed.

(* [comment removed for export] *)
Lemma pot_ae_split a kbb1 en1 sk1 :
  pot_ae L (AEST a kbb1 en1 sk1) = PM.credit_add (PQM.pot_adaptor L a) (PM.credit_add (pot_estack L (en_k en1)) (NESK.sink_pot NESK.PME (NESK.sk_c sk1))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_077 ())). Qed.
Lemma enc_pot_nonneg M o en1 sk1 : 0 <= en_k en1 <= EKMAX -> sink_at M o sk1 ->
  0 <= fst (PM.credit_add (pot_estack L (en_k en1)) (NESK.sink_pot NESK.PME (NESK.sk_c sk1)))
  /\ 0 <= snd (PM.credit_add (pot_estack L (en_k en1)) (NESK.sink_pot NESK.PME (NESK.sk_c sk1))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_078 ())). Qed.

Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r oa ov osk oec cat : Z) (bf ef : bool).
Variables (lv0 : list PQM.alvl) (c : PQM.alvl) (b k : Z) (key : PM.vstr) (kg : Z) (kb : PM.vstr) (kbg : Z) (kbb : list Z) (en : enc) (sk : NESK.sink).
Let lv : list PQM.alvl := lv0 ++ [c].
Let ast : PQM.ast := PQM.AST lv b k key kg kb kbg.
Let st : aest := AEST ast kbb en sk.
Let stW (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z) : PQM.ast := PQM.AST lv b k kx kgx kbx gx.
(* [comment removed for export] *)
Let ESO : list (Z * Z) := enc_own en ++ NESK.sink_own sk.
Let LBXe : list (Z * Z) := ESO ++ LBX.
Let n : Z := Z.of_nat (length lv0) + 1.
Let e0 : Z := b + 24 * n.
Hypothesis HH0 : hi_heap HI (aeown st ++ LBX) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 28672.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 oa.
Let KLN : Z := LITN.
Hypothesis A13 : getr R0 (reg 13) = Z_to_bv 64 oec.
Hypothesis Ho1 : S <= oa.
Hypothesis Ho2 : oa + PQM.ASIZE <= hl_sptop L.
Hypothesis Ho3 : oa mod 8 = 0.
Hypothesis Hov1 : S <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : oa + PQM.ASIZE <= ov.
Hypothesis Hovm : ov mod 8 = 0.
Hypothesis Hk1 : S <= osk.
Hypothesis Hk2 : osk + 24 <= hl_sptop L.
Hypothesis Hk3 : osk mod 8 = 0.
Hypothesis Hvk : ov + 56 <= osk.
Hypothesis He1 : S <= oec.
Hypothesis He2 : oec + 16 <= hl_sptop L.
Hypothesis He3 : oec mod 8 = 0.
Hypothesis He4 : oec + 16 <= oa.
Hypothesis AA0 : ae_at M0 oa ov osk st.
Hypothesis AOK0 : ae_ok st.
Hypothesis ECS0 : ec_state M0 oec bf cat.
Hypothesis BASE0 : PMST.base_ok RSEGS AD M0.
Hypothesis ERR0 : err_ok M0 ef.
Hypothesis PRE0 : PQM.kbsize ast + (KLN + 2) <= PQM.SMB.
Let dphi : Z := KLN + 2.
Hypothesis PREZ : NESK.sk_z sk + dphi <= NESK.SMZ.
Hypothesis CR0 : PMSP.credit_le (pot_ae L st) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (st' : aest) (b' e' : bool) (cr' : credit),
  regs_preserved R0 R' -> ae_at M' oa ov osk st' -> ae_ok st' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS AD M' -> err_ok M' e' ->
  (bf = true -> b' = true) -> (ef = true -> e' = true) ->
  (nlv st' = nlv st /\ kbsize st' <= kbsize st + (KLN + 2) /\ phi st' <= phi st + dphi /\ esize st' = esize st /\ edepth st' = edepth st /\ (b' = bf \/ False)) ->
  L5C.hpres L LBX S 28672 (ae_W AD oa ov osk oec) M0 M' ->
  PMSP.credit_keep cr0 cr' (pot_ae L st) (pot_ae L st') ->
  model_but_vm model0 model' -> hi_heap HI (aeown st' ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Lemma aeown_app : aeown st ++ LBX = PQM.aown ast ++ LBXe.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_079 ())). Qed.
Lemma BRXe : PMFR.brange L LBXe.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_080 ())). Qed.
Lemma BRX : PMFR.brange L LBX.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_081 ())). Qed.
Lemma VT0 : L5.u64_at RSEGS M0 ov (ne_vt AE).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_082 ())). Qed.
Let CX : PNADVK.ctx_ok L M0 K LBX S oa ov := conj K0 (conj STK0 (conj Ho1 (conj Ho2 (conj Ho3 (conj Hov1 (conj Hov2 (conj Hov3 (conj VT0 (conj BASE0 BRX))))))))).
Let CXe : PNADVK.ctx_ok L M0 K LBXe S oa ov := conj K0 (conj STK0 (conj Ho1 (conj Ho2 (conj Ho3 (conj Hov1 (conj Hov2 (conj Hov3 (conj VT0 (conj BASE0 BRXe))))))))).
Let CXO : S <= osk /\ osk + 24 <= hl_sptop L /\ osk mod 8 = 0 /\ S <= oec /\ oec + 16 <= hl_sptop L /\ oec mod 8 = 0 /\ oec + 16 <= oa /\ ov + 56 <= osk /\ ov mod 8 = 0 :=
  conj Hk1 (conj Hk2 (conj Hk3 (conj He1 (conj He2 (conj He3 (conj He4 (conj Hvk Hovm))))))).
Abbreviation cm := (PNADVK.cm L M0 LBX S oa ov osk oec).
Abbreviation cme := (PNADVK.cm L M0 LBXe S oa ov osk oec).
Abbreviation world := (PNADVK.world ov).
(* [comment removed for export] *)
Let KIT_frame0 := PNADVK.frame0 L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kcm_hpres := PNADVK.cm_hpres L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let Kcm0 := PNADVK.cm0 L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let Kcm_frz := PNADVK.cm_frz L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let Kworld0 := PNADVK.world0 L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kworld_frz := PNADVK.world_frz L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kworld_img := PNADVK.world_img L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kworld_vis := PNADVK.world_vis L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kad_split := PNADVK.ad_split L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kad_join := PNADVK.ad_join L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KHDR_keep := PNADVK.HDR_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KKEY_keep := PNADVK.KEY_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KKB_keep := PNADVK.KB_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KLV_keep := PNADVK.LV_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KLV_set_last := PNADVK.LV_set_last L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Ktop_cells := PNADVK.top_cells L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Ecm0 := PNADVK.cm0 L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let Ecm_frz := PNADVK.cm_frz L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EPBCALL := PNADVK.PBCALL L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EINSKB := PNADVK.INSKB L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EINSKEYC := PNADVKC.INSKEYC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EPBKEY := PNADVKC.PBKEYC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EPBCALLC := PNADVKC.PBCALLC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EINSKBC := PNADVKC.INSKBC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let KENC_SLOT := PNADEC.ENC_SLOT L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX CXO.
Let KENC_KEY := PNADEC.ENC_KEY L HI LY HIok OPN OPD VKE M0 K LBX S oa ov osk oec CX CXO.
Let ND : 1 <= KLN <= 20 := conj (proj1 (Z.leb_le 1 4) eq_refl) (proj1 (Z.leb_le 4 20) eq_refl).
(* [comment removed for export] *)
Lemma AAa0 : adaptor_at M0 oa ov ast.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_083 ())). Qed.
Lemma HHe0 : hi_heap HI (PQM.aown ast ++ LBXe) cr0 M0 (m_vmmaps model0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_084 ())). Qed.
Lemma ENK : 0 <= en_k en <= EKMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_085 ())). Qed.
(* [comment removed for export] *)
Lemma CRa0 : PMSP.credit_le (PQM.pot_adaptor L ast) cr0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_086 ())). Qed.

Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18)))
  /\ L5.u64_at RSEGS M (S - 40) (bv_unsigned (getr R0 (reg 19))).
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Lemma saves_keep M1 M2 : L5C.agree_on M1 M2 (S - 40) 40 -> saves M1 -> saves M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_087 ())). Qed.
Lemma blk : 4096 <= b /\ (b + 24 * 2 ^ k <= 0x10000 \/ 0xfa000 <= b) /\ b + 24 * 2 ^ k <= hl_ceil L /\ 0 <= k <= 11 /\ n <= 2 ^ k /\ b mod 16 = 0 /\ 1 <= 2 ^ k <= 2048 /\ 1 <= n <= 1025.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_088 ())). Qed.
Lemma e_facts : e0 = b + 24 * n /\ 4096 + 24 <= e0 /\ e0 <= b + 24 * 2 ^ k /\ b + 24 * 2 ^ k + 28672 <= S /\ e0 mod 8 = 0 /\ (e0 <= 0x10000 \/ 0xfa000 <= e0 - 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_089 ())). Qed.
Lemma c_ok : PQM.alvl_ok c /\ PQM.lv_shape lv /\ (PQM.lv_t c = 1 -> PQM.lv_k c <> 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_090 ())). Qed.
(* [comment removed for export] *)
Lemma own_lv a : b <= a < b + 24 * 2 ^ k -> a < hl_ceil L /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ ~ in_block LBXe a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_091 ())). Qed.
Lemma in_block_e a : ~ in_block LBXe a -> ~ in_block LBX a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_092 ())). Qed.
(* [comment removed for export] *)
Lemma cm_of_cme M : cme M -> cm M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_093 ())). Qed.
Lemma cs_restore (R1 R2 : bvmap 5 word) (KS : list nat) :
  kept0 R1 -> (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) -> forallb (fun x => existsb (Nat.eqb x) KS) [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat = true ->
  getr R2 (reg 2) = Z_to_bv 64 S -> getr R2 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R2 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R2 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) -> getr R2 (reg 19) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 19))) ->
  forall x, In x PMK.cs_all -> getr R2 (reg x) = getr R0 (reg x).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_094 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xinv (M : word -> option byte) (kbx : PM.vstr) (kbb1 : list Z) (en1 : enc) (sk1 : NESK.sink) (b1 e1 : bool) : Prop :=
  kcontent RSEGS M (oa + PQM.AOFF_KB) kbx kbb1 /\ utf8_valid kbb1 = true /\ enc_at M ov osk en1 /\ sink_at M osk sk1
  /\ ec_state M oec b1 cat /\ err_ok M e1 /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true)
  /\ en_n en1 = en_n en /\ en_depth en1 = en_depth en /\ (b1 = bf \/ False).
Lemma xinv0 : xinv M0 kb kbb en sk bf ef.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_095 ())). Qed.
(* [comment removed for export] *)
Lemma lv_apart M VM cr kx kgx kbx gx kbb1 en1 sk1 a :
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr M VM -> b <= a < b + 24 * 2 ^ k ->
  ~ in_block (PM.vs_own kx ++ PM.vs_own kbx ++ (enc_own en1 ++ NESK.sink_own sk1) ++ LBX) a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_096 ())). Qed.
(* [comment removed for export] *)
Lemma blocks_hi M VM cr kx kgx kbx gx kbb1 en1 sk1 B m :
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr M VM -> In (B, m) (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) ->
  4096 <= B /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\ B + m <= hl_ceil L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_097 ())). Qed.

(* [comment removed for export] *)
Lemma err_ok_frz M1 M2 (P : Z -> Prop) e1 :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> a < hl_img_lo L \/ hl_img_hi L <= a) -> err_ok M1 e1 -> err_ok M2 e1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_098 ())). Qed.

(* [comment removed for export] *)
Lemma xinv_frz M1 M2 (P : Z -> Prop) kx kgx kbx gx kbb1 en1 sk1 b1 e1 cr VM :
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr M1 VM -> adaptor_at M1 oa ov (stW kx kgx kbx gx) ->
  mem_grows M1 M2 -> (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> S - 28672 <= a < S \/ oa + 24 <= a < oa + 48 \/ b <= a < b + 24 * 2 ^ k \/ in_block (PM.vs_own kx) a) ->
  xinv M1 kbx kbb1 en1 sk1 b1 e1 -> xinv M2 kbx kbb1 en1 sk1 b1 e1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_099 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FIN (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (st' : aest) (b1 e1 : bool) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall x, In x PMK.cs_all -> getr R1 (reg x) = getr R0 (reg x)) ->
  ae_at M1 oa ov osk st' -> ae_ok st' -> ec_state M1 oec b1 cat -> PMST.base_ok RSEGS AD M1 -> err_ok M1 e1 ->
  (bf = true -> b1 = true) -> (ef = true -> e1 = true) ->
  (nlv st' = nlv st /\ kbsize st' <= kbsize st + (KLN + 2) /\ phi st' <= phi st + dphi /\ esize st' = esize st /\ edepth st' = edepth st /\ (b1 = bf \/ False)) ->
  cm M1 -> PMSP.credit_keep cr0 cr1 (pot_ae L st) (pot_ae L st') -> model_but_vm model0 model1 ->
  hi_heap HI (aeown st' ++ LBX) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3b690 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_100 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ADV (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z)
      (kbb1 : list Z) (en1 : enc) (sk1 : NESK.sink) (b1 e1 : bool) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa -> kept0 R1 ->
  saves M1 -> cm M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kbx gx) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx <= PM.vs_size kb + (KLN + 2) ->
  xinv M1 kbx kbb1 en1 sk1 b1 e1 -> NESK.sk_z sk1 + PM.vs_size kbx <= NESK.sk_z sk + PM.vs_size kb + dphi ->
  PMSP.credit_keep cr0 cr1 (pot_ae L st) (pot_ae L (AEST (stW kx kgx kbx gx) kbb1 en1 sk1)) -> model_but_vm model0 model1 ->
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3b648 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_101 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma long_facts M o cc mm qq LL cr VM :
  kstr_at M o (PM.VLong cc mm qq) -> In (qq, cc) LL -> hi_heap HI LL cr M VM ->
  L5.u8_at RSEGS M o ((cc + 1) mod 256) /\ 0 <= (cc + 1) mod 256 <= 255 /\ Z.testbit ((cc + 1) mod 256) 0 = true /\ L5.u64_at RSEGS M (o + 8) mm /\ L5.u64_at RSEGS M (o + 16) qq
  /\ 0 <= mm < cc /\ 26 <= cc <= PQM.KCAP /\ 4096 <= qq /\ qq + cc <= hl_ceil L /\ (qq + cc <= 0x10000 \/ 0xfa000 <= qq) /\ L5.defined M qq cc /\ L5.writable RSEGS M qq 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_102 ())). Qed.
Lemma short_facts M o mm : kstr_at M o (PM.VShort mm) -> L5.u8_at RSEGS M o (2 * mm) /\ 0 <= mm <= 22 /\ 0 <= Z.land ((2 * mm) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_103 ())). Qed.
(* [comment removed for export] *)
Lemma prep (M : word -> option byte) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z) :
  cm M -> adaptor_at M oa ov (stW kx kgx kbx gx) ->
  L5.writable RSEGS M (S - 64) 64 /\ L5.writable RSEGS M (oa + 24) 72 /\ L5.writable RSEGS M (e0 - 24) 24 /\ L5.u64_at RSEGS M (oa + 80) e0
  /\ L5.u32_at RSEGS M (e0 - 24) (PQM.lv_t c) /\ L5.u32_at RSEGS M (e0 - 20) (PQM.lv_k c) /\ L5.u32_at RSEGS M (e0 - 16) (PQM.lv_eo c) /\ L5.defined M (e0 - 8) 8
  /\ L5.u64_at RSEGS M (oa + 16) ov /\ PNADVK.KEY oa M kx /\ PNADVK.KB oa M kbx.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_104 ())). Qed.
Lemma cme_cm M : cme M -> cm M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_105 ())). Qed.

(* [comment removed for export] *)
Lemma MAIN_D : PQM.lv_eo c = 1 -> PQM.lv_t c = 0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b424 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_106 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aeown_appW a kbb1 : aeown (AEST a kbb1 en sk) ++ LBX = PQM.aown a ++ LBXe.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_107 ())). Qed.
(* [comment removed for export] *)
Lemma kc_frz M1 M2 (P : Z -> Prop) kx kgx kbx gx kcs cr VM :
  hi_heap HI (PQM.aown (stW kx kgx kbx gx) ++ LBXe) cr M1 VM -> adaptor_at M1 oa ov (stW kx kgx kbx gx) ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> S - 28672 <= a < S \/ b <= a < b + 24 * 2 ^ k) ->
  kcontent RSEGS M1 (oa + 24) kx kcs -> kcontent RSEGS M2 (oa + 24) kx kcs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_108 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma KEYDEST (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kcs : list Z) (cr1 : credit) :
  PQM.lv_eo c = 0 -> PQM.lv_t c = 0 ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 oec -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kb kbg) -> kcontent RSEGS M1 (oa + 24) kx kcs -> ascii kcs ->
  PQM.ks_ok PQM.SMK kx kgx -> PM.vs_size kx = KLN -> xinv M1 kb kbb en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW kx kgx kb kbg)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW kx kgx kb kbg) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3b4b8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_109 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma xinv_call M Mq kbx kbb1 kbx' kbb' b1 e1 (lo wlo : Z) :
  lo <= S -> (wlo = oa + 24 \/ wlo = oa + 48) ->
  (forall a m, lo <= a -> a + m <= 2 ^ 64 -> (a + m <= wlo \/ wlo + 24 <= a) -> L5C.agree_on M Mq a m) ->
  (forall B m, In (B, m) LBXe -> L5C.agree_on M Mq B m) ->
  (forall e, err_ok M e -> err_ok Mq e) ->
  kcontent RSEGS Mq (oa + PQM.AOFF_KB) kbx' kbb' -> utf8_valid kbb' = true ->
  xinv M kbx kbb1 en sk b1 e1 -> xinv Mq kbx' kbb' en sk b1 e1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_110 ())). Qed.
(* [comment removed for export] *)
Lemma kbc_keyop M Mq kx kgx kbx gx kbb1 lo cr Mh VM :
  adaptor_at M oa ov (stW kx kgx kbx gx) -> hi_heap HI (PQM.aown (stW kx kgx kbx gx) ++ LBXe) cr Mh VM -> lo <= S ->
  (forall a m, lo <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 24 \/ oa + 48 <= a) -> L5C.agree_on M Mq a m) ->
  (forall B m, In (B, m) (PQM.lvec_own b k ++ PM.vs_own kbx ++ LBXe) -> L5C.agree_on M Mq B m) ->
  kcontent RSEGS M (oa + PQM.AOFF_KB) kbx kbb1 -> kcontent RSEGS Mq (oa + PQM.AOFF_KB) kbx kbb1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_111 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dphi_ge : KLN + 2 <= dphi.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_112 ())). Qed.
Lemma ascii_1 ch : 0 <= ch < 128 -> ascii [ch].
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_113 ())). Qed.
(* [comment removed for export] *)
Lemma kc_kbop M Mq kx kgx kbx gx kcs lo cr Mh VM :
  adaptor_at M oa ov (stW kx kgx kbx gx) -> hi_heap HI (PQM.aown (stW kx kgx kbx gx) ++ LBXe) cr Mh VM -> lo <= S ->
  (forall a m, lo <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 48 \/ oa + 72 <= a) -> L5C.agree_on M Mq a m) ->
  (forall B m, In (B, m) (PQM.lvec_own b k ++ PM.vs_own kx ++ LBXe) -> L5C.agree_on M Mq B m) ->
  kcontent RSEGS M (oa + 24) kx kcs -> kcontent RSEGS Mq (oa + 24) kx kcs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_114 ())). Qed.

(* [comment removed for export] *)
Lemma TOADV (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z) (kbb1 : list Z) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kbx gx) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx <= PM.vs_size kb + (KLN + 2) ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW kx kgx kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW kx kgx kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3b5c0 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_115 ())). Qed.

(* [comment removed for export] *)
Lemma COLON (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z) (kbb1 : list Z) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 (oa + 48) -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kbx gx) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx <= PM.vs_size kb + (KLN + 1) ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW kx kgx kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW kx kgx kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3b63c M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_116 ())). Qed.

(* [comment removed for export] *)
Lemma INS2 (isK : bool) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z)
      (kcs kbb1 : list Z) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa -> (isK = false -> getr R1 (reg 9) = Z_to_bv 64 (oa + 48)) -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kbx gx) -> kcontent RSEGS M1 (oa + 24) kx kcs -> ascii kcs ->
  PQM.ks_ok PQM.SMK kx kgx -> PM.vs_size kx = KLN -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx <= PM.vs_size kb + 1 ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW kx kgx kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW kx kgx kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if isK then 0x3b54c else 0x3b4f4) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_117 ())). Qed.

(* [comment removed for export] *)
Lemma COMMA (isK : bool) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kcs : list Z) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 (if isK then 0x3b54c else 0x3b4f4) -> getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa ->
  (isK = false -> getr R1 (reg 9) = Z_to_bv 64 (oa + 48)) -> getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 44 -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kb kbg) -> kcontent RSEGS M1 (oa + 24) kx kcs -> ascii kcs ->
  PQM.ks_ok PQM.SMK kx kgx -> PM.vs_size kx = KLN -> xinv M1 kb kbb en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW kx kgx kb kbg)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW kx kgx kb kbg) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66444 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_118 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DISP (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kcs : list Z) (cr1 : credit) :
  (PQM.lv_eo c = 0 \/ PQM.lv_t c = 1) ->
  getr R1 (reg 2) = Z_to_bv 64 (S - 64) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 oec -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kb kbg) -> kcontent RSEGS M1 (oa + 24) kx kcs -> ascii kcs ->
  PQM.ks_ok PQM.SMK kx kgx -> PM.vs_size kx = KLN -> xinv M1 kb kbb en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW kx kgx kb kbg)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW kx kgx kb kbg) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3b4b8 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_119 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pk_facts ck mk pk : PM.VLong ck mk pk = key ->
  L5.u8_at RSEGS M0 (oa + 24) ((ck + 1) mod 256) /\ 0 <= (ck + 1) mod 256 <= 255 /\ Z.testbit ((ck + 1) mod 256) 0 = true /\ L5.u64_at RSEGS M0 (oa + 32) mk /\ L5.u64_at RSEGS M0 (oa + 40) pk
  /\ 0 <= mk < ck /\ 26 <= ck <= PQM.KCAP /\ 4096 <= pk /\ pk + ck <= hl_ceil L /\ (pk + ck <= 0x10000 \/ 0xfa000 <= pk) /\ L5.defined M0 pk ck /\ L5.writable RSEGS M0 pk 1
  /\ ~ in_block LBXe pk /\ ~ (b <= pk < b + 24 * 2 ^ k) /\ PMK.cwr L (aeown st ++ LBX) pk.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_120 ())). Qed.

(* [comment removed for export] *)
Lemma MAIN_K (cc : bool) : (if cc then PQM.lv_t c = 1 /\ PQM.lv_eo c = 1 else PQM.lv_eo c = 0) -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b424 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_121 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MAIN : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b424 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_122 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem null_ok : PNV.v_null_spec RSEGS AD AQ AE L HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSNl ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_123 ())). Qed.

End WithHeap.
End PNADNL.

End PnAdSNl.
Module PnAdSVsP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSVsP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA015regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA019regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib6ZArith6BinInt1Z3subc69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=word_of_zpolyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KUnkC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA01<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA013PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA012F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA013NX0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA013kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA013ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsA01_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA115regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA119regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA11C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA11<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA113PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA112F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA113NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA113kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA113ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsA11_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA205regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA209regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA20C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA20<seg_sound_axC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_Inc69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>u32_of_KWord4aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA203PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA202F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA203NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA203kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA203ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsA20_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA206cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA215regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA219regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsA21C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA21<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA213PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA212F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA213NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA213kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA213ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsA21_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsA216cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsCkC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsCk3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=KS_ad_vsCk_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsEd2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;kentry_KImgC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd2<seg_sound_axC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEd23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsEd2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsEk2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk2<seg_sound_axC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsEk23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsEk2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIkL2C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?land1_bit0_trueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5KDkentry_KRange_andlitC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL23NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkL23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP?KS_ad_vsIkL2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIkS2C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05K59OSSVerify5KrLib;BigLinkBase2BL2za02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib;BigLinkBase2BL2za0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL5zcompC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL2uvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL4zdenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8zc_soundC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS23NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01I59OSSVerify5KrLib;BigLinkBase2BL2za00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIkS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP?KS_ad_vsIkS2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIvL2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvL23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP?KS_ad_vsIvL2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIvS2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:Pad_vsIvS23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP?KS_ad_vsIvS2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsKnC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKn3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=KS_ad_vsKn_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsKzC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsKz3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=KS_ad_vsKz_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ1kC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1k3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsQ1k_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ1vC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ1v3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsQ1v_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ2kC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2k3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsQ2k_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ2vC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsQ2v3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsQ2v_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsR1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=KS_ad_vsR1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsR2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsR23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=KS_ad_vsR2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsV1nC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1n3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsV1n_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsV1zC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsV1z3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsV1z_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsV2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP8Pad_vsV23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=KS_ad_vsV2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsZ0LC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0L3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsZ0L_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsZ0SC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP9Pad_vsZ0S3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>KS_ad_vsZ0S_okC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PQADVSP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_124 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_125 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_126 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_127 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_128 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_129 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_130 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_131 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_132 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_133 ())). Qed.
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
Module Pad_vsA01 := BndP_Ns_039.LibSegNs_ad_vsA01.
Definition KS_ad_vsA01 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsA01.regs0 Pad_vsA01.regs_out0).
Lemma KS_ad_vsA01_ok : BG.kept_ok 64 Pad_vsA01.regs0 Pad_vsA01.regs_out0 KS_ad_vsA01 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_134 ())). Qed.
Lemma ad_vsA01_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 0 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba98 M) (st fx' R' 0x3badc M')
        /\ (forall x, In x KS_ad_vsA01 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_135 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsA11 := BndP_Ns_039.LibSegNs_ad_vsA11.
Definition KS_ad_vsA11 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsA11.regs0 Pad_vsA11.regs_out0).
Lemma KS_ad_vsA11_ok : BG.kept_ok 64 Pad_vsA11.regs0 Pad_vsA11.regs_out0 KS_ad_vsA11 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_136 ())). Qed.
Lemma ad_vsA11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba98 M) (st fx' R' 0x3badc M')
        /\ (forall x, In x KS_ad_vsA11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_137 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsA20 := BndP_Ns_039.LibSegNs_ad_vsA20.
Definition KS_ad_vsA20 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsA20.regs0 Pad_vsA20.regs_out0).
Lemma KS_ad_vsA20_ok : BG.kept_ok 64 Pad_vsA20.regs0 Pad_vsA20.regs_out0 KS_ad_vsA20 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_138 ())). Qed.
Lemma ad_vsA20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba98 M) (st fx' R' 0x3badc M')
        /\ (forall x, In x KS_ad_vsA20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 1).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_139 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsA21 := BndP_Ns_039.LibSegNs_ad_vsA21.
Definition KS_ad_vsA21 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsA21.regs0 Pad_vsA21.regs_out0).
Lemma KS_ad_vsA21_ok : BG.kept_ok 64 Pad_vsA21.regs0 Pad_vsA21.regs_out0 KS_ad_vsA21 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_140 ())). Qed.
Lemma ad_vsA21_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  L5.defined M ((V 37%nat) - 8) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 43%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) - 8) <= bv_unsigned a < ((V 37%nat) - 8) + 8) -> ~ (((V 37%nat) - 16) <= bv_unsigned a < ((V 37%nat) - 16) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) - 8) <= i < ((V 37%nat) - 8) + 8) -> ~ (((V 37%nat) - 16) <= i < ((V 37%nat) - 16) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba98 M) (st fx' R' 0x3badc M')
        /\ (forall x, In x KS_ad_vsA21 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 13) = Z_to_bv 64 2
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ L5.u32_at RSEGS M' ((V 37%nat) - 16) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_141 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsCk := BndP_Ns_039.LibSegNs_ad_vsCk.
Definition KS_ad_vsCk : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsCk.regs0 Pad_vsCk.regs_out0).
Lemma KS_ad_vsCk_ok : BG.kept_ok 64 Pad_vsCk.regs0 Pad_vsCk.regs_out0 KS_ad_vsCk = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_142 ())). Qed.
Lemma ad_vsCk_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba8c M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsCk -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244376
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 58).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_143 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsEd2 := BndP_Ns_039.LibSegNs_ad_vsEd2.
Definition KS_ad_vsEd2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsEd2.regs0 Pad_vsEd2.regs_out0).
Lemma KS_ad_vsEd2_ok : BG.kept_ok 64 Pad_vsEd2.regs0 Pad_vsEd2.regs_out0 KS_ad_vsEd2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_144 ())). Qed.
Lemma ad_vsEd2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 37%nat) - 24)) -> (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> 140735332483104 <= (V 38%nat) <= 140737488355272 -> (((V 2%nat) - 32) + 32 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 38%nat) 785968 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> L5.img_clear M 65536 814272 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x408d8 M')
        /\ (forall x, In x KS_ad_vsEd2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244236
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 264408
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_145 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsEk2 := BndP_Ns_039.LibSegNs_ad_vsEk2.
Definition KS_ad_vsEk2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsEk2.regs0 Pad_vsEk2.regs_out0).
Lemma KS_ad_vsEk2_ok : BG.kept_ok 64 Pad_vsEk2.regs0 Pad_vsEk2.regs_out0 KS_ad_vsEk2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_146 ())). Qed.
Lemma ad_vsEk2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 37%nat) - 24)) -> (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 0 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 0 -> 140735332483104 <= (V 38%nat) <= 140737488355272 -> (((V 2%nat) - 32) + 32 <= (V 38%nat) \/ (V 38%nat) + 56 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= (V 38%nat) \/ (V 38%nat) + 56 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 38%nat) 785968 -> L5.u64_at RSEGS M ((V 36%nat) + 16) (V 38%nat) -> L5.img_clear M 65536 814272 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x40810 M')
        /\ (forall x, In x KS_ad_vsEk2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244268
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 12) = getr R (reg 13)
        /\ getr R' (reg 13) = getr R (reg 14)
        /\ getr R' (reg 15) = Z_to_bv 64 264208
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_147 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsIkL2 := BndP_Ns_039.LibSegNs_ad_vsIkL2.
Definition KS_ad_vsIkL2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsIkL2.regs0 Pad_vsIkL2.regs_out0).
Lemma KS_ad_vsIkL2_ok : BG.kept_ok 64 Pad_vsIkL2.regs0 Pad_vsIkL2.regs_out0 KS_ad_vsIkL2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_148 ())). Qed.
Lemma ad_vsIkL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 50%nat) ->
  0 <= (V 50%nat) <= 255 -> Z.testbit (V 50%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 52%nat) ->
  0 <= (V 51%nat) <= 2147483648 -> 4096 <= (V 52%nat) <= 140737487306752 -> 140735332483104 <= (V 55%nat) <= 140737488355312 -> (((V 2%nat) - 32) + 32 <= (V 55%nat) \/ (V 55%nat) + 16 <= ((V 2%nat) - 32)) ->
  ((V 36%nat) + 96 <= (V 55%nat) \/ (V 55%nat) + 16 <= (V 36%nat)) -> L5.u64_at RSEGS M (V 55%nat) (V 56%nat) -> L5.u64_at RSEGS M ((V 55%nat) + 8) (V 57%nat) -> 0 <= (V 56%nat) <= 18446744073709551615 ->
  0 <= (V 57%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b9dc M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_vsIkL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244352
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 51%nat) + (V 52%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 56%nat) + (V 57%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 57%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_149 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsIkS2 := BndP_Ns_039.LibSegNs_ad_vsIkS2.
Definition KS_ad_vsIkS2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsIkS2.regs0 Pad_vsIkS2.regs_out0).
Lemma KS_ad_vsIkS2_ok : BG.kept_ok 64 Pad_vsIkS2.regs0 Pad_vsIkS2.regs_out0 KS_ad_vsIkS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_150 ())). Qed.
Lemma ad_vsIkS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (2 * (V 49%nat)) ->
  0 <= (V 49%nat) <= 22 -> 0 <= (Z.land ((2 * (V 49%nat)) mod 2 ^ 64) 1) <= 0 -> 140735332483104 <= (V 55%nat) <= 140737488355312 -> (((V 2%nat) - 32) + 32 <= (V 55%nat) \/ (V 55%nat) + 16 <= ((V 2%nat) - 32)) ->
  ((V 36%nat) + 96 <= (V 55%nat) \/ (V 55%nat) + 16 <= (V 36%nat)) -> L5.u64_at RSEGS M (V 55%nat) (V 56%nat) -> L5.u64_at RSEGS M ((V 55%nat) + 8) (V 57%nat) -> 0 <= (V 56%nat) <= 18446744073709551615 ->
  0 <= (V 57%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b9dc M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_vsIkS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244352
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 49%nat)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 56%nat) + (V 57%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 57%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_151 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsIvL2 := BndP_Ns_039.LibSegNs_ad_vsIvL2.
Definition KS_ad_vsIvL2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsIvL2.regs0 Pad_vsIvL2.regs_out0).
Lemma KS_ad_vsIvL2_ok : BG.kept_ok 64 Pad_vsIvL2.regs0 Pad_vsIvL2.regs_out0 KS_ad_vsIvL2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_152 ())). Qed.
Lemma ad_vsIvL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (V 50%nat) ->
  0 <= (V 50%nat) <= 255 -> Z.testbit (V 50%nat) 0 = true -> L5.u64_at RSEGS M ((V 36%nat) + 56) (V 51%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 64) (V 52%nat) ->
  0 <= (V 51%nat) <= 2147483648 -> 4096 <= (V 52%nat) <= 140737487306752 -> 140735332483104 <= (V 55%nat) <= 140737488355312 -> (((V 2%nat) - 32) + 32 <= (V 55%nat) \/ (V 55%nat) + 16 <= ((V 2%nat) - 32)) ->
  ((V 36%nat) + 96 <= (V 55%nat) \/ (V 55%nat) + 16 <= (V 36%nat)) -> L5.u64_at RSEGS M (V 55%nat) (V 56%nat) -> L5.u64_at RSEGS M ((V 55%nat) + 8) (V 57%nat) -> 0 <= (V 56%nat) <= 18446744073709551615 ->
  0 <= (V 57%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b998 M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_vsIvL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244308
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 51%nat) + (V 52%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 56%nat) + (V 57%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 57%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_153 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsIvS2 := BndP_Ns_039.LibSegNs_ad_vsIvS2.
Definition KS_ad_vsIvS2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsIvS2.regs0 Pad_vsIvS2.regs_out0).
Lemma KS_ad_vsIvS2_ok : BG.kept_ok 64 Pad_vsIvS2.regs0 Pad_vsIvS2.regs_out0 KS_ad_vsIvS2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_154 ())). Qed.
Lemma ad_vsIvS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> L5.u8_at RSEGS M ((V 36%nat) + 48) (2 * (V 49%nat)) ->
  0 <= (V 49%nat) <= 22 -> 0 <= (Z.land ((2 * (V 49%nat)) mod 2 ^ 64) 1) <= 0 -> 140735332483104 <= (V 55%nat) <= 140737488355312 -> (((V 2%nat) - 32) + 32 <= (V 55%nat) \/ (V 55%nat) + 16 <= ((V 2%nat) - 32)) ->
  ((V 36%nat) + 96 <= (V 55%nat) \/ (V 55%nat) + 16 <= (V 36%nat)) -> L5.u64_at RSEGS M (V 55%nat) (V 56%nat) -> L5.u64_at RSEGS M ((V 55%nat) + 8) (V 57%nat) -> 0 <= (V 56%nat) <= 18446744073709551615 ->
  0 <= (V 57%nat) <= 1073741824 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b998 M) (st fx' R' 0x3e908 M')
        /\ (forall x, In x KS_ad_vsIvS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244308
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 49%nat)) + 49)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 56%nat) + (V 57%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 (V 57%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_155 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsKn := BndP_Ns_039.LibSegNs_ad_vsKn.
Definition KS_ad_vsKn : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsKn.regs0 Pad_vsKn.regs_out0).
Lemma KS_ad_vsKn_ok : BG.kept_ok 64 Pad_vsKn.regs0 Pad_vsKn.regs_out0 KS_ad_vsKn = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_156 ())). Qed.
Lemma ad_vsKn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.u64_at RSEGS M ((V 37%nat) - 8) (V 39%nat) -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsKn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244172
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_157 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsKz := BndP_Ns_039.LibSegNs_ad_vsKz.
Definition KS_ad_vsKz : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsKz.regs0 Pad_vsKz.regs_out0).
Lemma KS_ad_vsKz_ok : BG.kept_ok 64 Pad_vsKz.regs0 Pad_vsKz.regs_out0 KS_ad_vsKz = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_158 ())). Qed.
Lemma ad_vsKz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 16) 0 ->
  L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsKz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244188
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_159 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsQ1k := BndP_Ns_039.LibSegNs_ad_vsQ1k.
Definition KS_ad_vsQ1k : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsQ1k.regs0 Pad_vsQ1k.regs_out0).
Lemma KS_ad_vsQ1k_ok : BG.kept_ok 64 Pad_vsQ1k.regs0 Pad_vsQ1k.regs_out0 KS_ad_vsQ1k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_160 ())). Qed.
Lemma ad_vsQ1k_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b9cc M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsQ1k -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244188
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 48)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_161 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsQ1v := BndP_Ns_040.LibSegNs_ad_vsQ1v.
Definition KS_ad_vsQ1v : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsQ1v.regs0 Pad_vsQ1v.regs_out0).
Lemma KS_ad_vsQ1v_ok : BG.kept_ok 64 Pad_vsQ1v.regs0 Pad_vsQ1v.regs_out0 KS_ad_vsQ1v = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_162 ())). Qed.
Lemma ad_vsQ1v_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b98c M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsQ1v -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244120
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_163 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsQ2k := BndP_Ns_040.LibSegNs_ad_vsQ2k.
Definition KS_ad_vsQ2k : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsQ2k.regs0 Pad_vsQ2k.regs_out0).
Lemma KS_ad_vsQ2k_ok : BG.kept_ok 64 Pad_vsQ2k.regs0 Pad_vsQ2k.regs_out0 KS_ad_vsQ2k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_164 ())). Qed.
Lemma ad_vsQ2k_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba80 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsQ2k -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244364
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_165 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsQ2v := BndP_Ns_040.LibSegNs_ad_vsQ2v.
Definition KS_ad_vsQ2v : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsQ2v.regs0 Pad_vsQ2v.regs_out0).
Lemma KS_ad_vsQ2v_ok : BG.kept_ok 64 Pad_vsQ2v.regs0 Pad_vsQ2v.regs_out0 KS_ad_vsQ2v = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_166 ())). Qed.
Lemma ad_vsQ2v_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 36%nat) -> getr R (reg 9) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 36%nat) + 48) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba54 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsQ2v -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244376
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_167 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsR1 := BndP_Ns_040.LibSegNs_ad_vsR1.
Definition KS_ad_vsR1 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsR1.regs0 Pad_vsR1.regs_out0).
Lemma KS_ad_vsR1_ok : BG.kept_ok 64 Pad_vsR1.regs0 Pad_vsR1.regs_out0 KS_ad_vsR1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_168 ())). Qed.
Lemma ad_vsR1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba0c M) (st fx' R' 0x3ba98 M')
        /\ (forall x, In x KS_ad_vsR1 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_169 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsR2 := BndP_Ns_040.LibSegNs_ad_vsR2.
Definition KS_ad_vsR2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsR2.regs0 Pad_vsR2.regs_out0).
Lemma KS_ad_vsR2_ok : BG.kept_ok 64 Pad_vsR2.regs0 Pad_vsR2.regs_out0 KS_ad_vsR2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_170 ())). Qed.
Lemma ad_vsR2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3ba2c M) (st fx' R' 0x3ba98 M')
        /\ (forall x, In x KS_ad_vsR2 -> getr R' (reg x) = getr R (reg x))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_171 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsV1n := BndP_Ns_040.LibSegNs_ad_vsV1n.
Definition KS_ad_vsV1n : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsV1n.regs0 Pad_vsV1n.regs_out0).
Lemma KS_ad_vsV1n_ok : BG.kept_ok 64 Pad_vsV1n.regs0 Pad_vsV1n.regs_out0 KS_ad_vsV1n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_172 ())). Qed.
Lemma ad_vsV1n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) (V 39%nat) -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsV1n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 44
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_173 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsV1z := BndP_Ns_040.LibSegNs_ad_vsV1z.
Definition KS_ad_vsV1z : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsV1z.regs0 Pad_vsV1z.regs_out0).
Lemma KS_ad_vsV1z_ok : BG.kept_ok 64 Pad_vsV1z.regs0 Pad_vsV1z.regs_out0 KS_ad_vsV1z = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_174 ())). Qed.
Lemma ad_vsV1z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 1 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 -> L5.u64_at RSEGS M ((V 37%nat) - 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsV1z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244120
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_175 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsV2 := BndP_Ns_040.LibSegNs_ad_vsV2.
Definition KS_ad_vsV2 : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsV2.regs0 Pad_vsV2.regs_out0).
Lemma KS_ad_vsV2_ok : BG.kept_ok 64 Pad_vsV2.regs0 Pad_vsV2.regs_out0 KS_ad_vsV2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_176 ())). Qed.
Lemma ad_vsV2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 55%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483104 <= (V 36%nat) <= 140737488355232 ->
  aligned (V 36%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 36%nat) \/ (V 36%nat) + 96 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 36%nat) + 24) 72 -> 4120 <= (V 37%nat) <= 140737487306752 ->
  aligned (V 37%nat) 8 -> L5.writable RSEGS M ((V 37%nat) - 24) 24 -> (((V 2%nat) - 32) + 32 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= ((V 2%nat) - 32)) -> ((V 36%nat) + 96 <= ((V 37%nat) - 24) \/ ((V 37%nat) - 24) + 24 <= (V 36%nat)) ->
  (((V 37%nat) - 24) + 24 <= 65536 \/ 65536 + 958464 <= ((V 37%nat) - 24)) -> L5.u64_at RSEGS M ((V 36%nat) + 80) (V 37%nat) -> L5.u32_at RSEGS M ((V 37%nat) - 24) 1 -> L5.u32_at RSEGS M ((V 37%nat) - 20) 2 ->
  L5.u32_at RSEGS M ((V 37%nat) - 16) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3b934 M) (st fx' R' 0x66444 M')
        /\ (forall x, In x KS_ad_vsV2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 244120
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 34
        /\ getr R' (reg 12) = Z_to_bv 64 2
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 36%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_177 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsZ0L := BndP_Ns_040.LibSegNs_ad_vsZ0L.
Definition KS_ad_vsZ0L : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsZ0L.regs0 Pad_vsZ0L.regs_out0).
Lemma KS_ad_vsZ0L_ok : BG.kept_ok 64 Pad_vsZ0L.regs0 Pad_vsZ0L.regs_out0 KS_ad_vsZ0L = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_178 ())). Qed.
Lemma ad_vsZ0L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) -> getr R (reg 14) = Z_to_bv 64 0 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 35%nat) <= 140737488355304 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 35%nat) \/ (V 35%nat) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (V 35%nat) 24 -> L5.u8_at RSEGS M (V 35%nat) (V 46%nat) ->
  0 <= (V 46%nat) <= 255 -> Z.testbit (V 46%nat) 0 = true -> L5.u64_at RSEGS M ((V 35%nat) + 16) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea1c M')
        /\ (forall x, In x KS_ad_vsZ0L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_179 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pad_vsZ0S := BndP_Ns_040.LibSegNs_ad_vsZ0S.
Definition KS_ad_vsZ0S : list nat := Eval vm_compute in (BG.kept_list 64 Pad_vsZ0S.regs0 Pad_vsZ0S.regs_out0).
Lemma KS_ad_vsZ0S_ok : BG.kept_ok 64 Pad_vsZ0S.regs0 Pad_vsZ0S.regs_out0 KS_ad_vsZ0S = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_180 ())). Qed.
Lemma ad_vsZ0S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 (V 38%nat) -> getr R (reg 14) = Z_to_bv 64 0 ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483136 <= (V 35%nat) <= 140737488355304 ->
  aligned (V 35%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 35%nat) \/ (V 35%nat) + 24 <= ((V 2%nat) - 64)) -> L5.writable RSEGS M (V 35%nat) 24 -> L5.u8_at RSEGS M (V 35%nat) (2 * (V 34%nat)) ->
  0 <= (V 34%nat) <= 22 -> 0 <= (Z.land ((2 * (V 34%nat)) mod 2 ^ 64) 1) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3e908 M) (st fx' R' 0x3ea1c M')
        /\ (forall x, In x KS_ad_vsZ0S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (2 * (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVsP ()) [] (Mh_0192_blobs1.kr_b_181 ())). Qed.
(* [comment removed for export] *)

End PQADVSP.

End PnAdSVsP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.
Module PnAdSVs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnAdECall. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVis OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnVisN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.WdSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnMpKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnMpBaKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnAdStr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdKit2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPb OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSIns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdLvKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnMpKitN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitN OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnAdECall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnAdStrC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSPbC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdVKitC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0188.PnAdSJnsC OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0192.PnAdSVsP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r3b418_3b41c OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0021.Ns0_code_r3e358_3e35c.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef Utf8Facts.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnAdSVs () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4kclrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_sizeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM7vs_dataC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00907PmModel2PM4vstr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ks_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4GMAXC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM;pot_adaptorC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM4alvl00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4aownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:pot_estackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM:credit_addC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028PnQModel3PQM3ast00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3PMEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK<sink_pot_fstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK?sink_pot_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_kpmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface?hl_k_per_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6ly_bovC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface=hl_b_overheadC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t03C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK6PME_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_01028NemModel3NEM5aeownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC46Stdlib5Lists4List4inclC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS9aeown_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appK47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4BRXeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ=qa_vp_adaptorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6ae_kbbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8kcontentC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:PnLayoutQS7QADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6pot_aeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS<pot_ae_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS>enc_pot_nonnegC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9cle_add_rC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3ENKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5savesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<u64_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9TAG_ENANOC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib7Mh_00188PmLayout=pa_vp_visitorC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7kstr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_lvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lvec_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_atC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib7Mh_00907PmModel2PM6vs_ownC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS9ly_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmModel2PM8pow2_posC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ae_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:adaptor_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6UbjRef:utf8_validC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ndestC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lv_shapeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4a_kgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5a_kbgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_kC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib7Mh_01028PnQModel3PQM7alvl_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_lec69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4AAa0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_DVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9AOFF_DESTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5ASIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8AOFF_KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7AOFF_LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3LSZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM7lv_rootC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4HHe0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM3SMBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9MAX_DEPTHC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3blkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C46Stdlib5Lists4List8app_nth2C69OSSVerify5KrLib7Mh_01028PnQModel3PQM4lv_tC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3subC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C46Stdlib5Lists4ListClength_zero_iff_nilC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib7Mh_00849HeapIface8in_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01427PnAdKit4PQAK:own_not_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2cmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ae_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9ek_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;client_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8in_errnoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK;client_monoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5kept0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK6sub_inC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK8reg_backC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4xinvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib7Mh_00188PmLayout?pa_errcat_guardC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST9atexit_stC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;u8_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP;clear_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP5sf_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout9pa_atexitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST<atexit_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3HDRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3KEYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2KBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK2LVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM8lvec_ownC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS9blocks_hiC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orK46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppc69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8lv_apartC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;PermutationHPermutation_app_swap_appC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK9heap_permC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnMpKitN4PNMK>kcontent_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT<enc_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT=sink_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT>ec_state_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:err_ok_frzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3nlvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6kbsizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3phiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5esizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM6edepthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=halted_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C;lazy_but_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib7Mh_01356PmStep3PMK6ret_toC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMKBpreserved_by_indexC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01028NemModel3NEM4aest00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r3b418_3b41c7W_3ba94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r3b418_3b41c7F_3ba94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r3b418_3b41c7D_3ba94C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF9u8_of_u64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090<PmModelFacts3PMF8odd_byteC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC69OSSVerify5KrLib7Mh_01028PnQModel3PQM4KCAPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK7land2_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM5lv_eoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS7e_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS9cm_of_cmeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3BRXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4VIEWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C=defined_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS9VIEW_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8vw_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK5worldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cwrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM9adaptor_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:aeown_appWC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS7ck_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CAmodel_but_vm_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS;short_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitN6PNADVK3G64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP7alignedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01358PmParKit4PMPK6m8_addC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsZ0S_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:long_factsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsZ0L_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK8stk_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM:pot_vstackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028PnQModel3PQM6pot_ksC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS9cle_add_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFRBoutside_of_not_inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP:kept_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmKeep4PMKP:kept_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC7src_okCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01428PnAdStrC5PQASC9ins_specCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906WdSpec2WD9entry_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_add_lC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C69OSSVerify5KrLib7Mh_00906L5Core3L5C4keptC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_00906WdSpec2WD6PB_SCRC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7W_3e9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7F_3e9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0021ENs0_code_r3e358_3e35c7D_3e9d4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsZ0SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsZ0LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K3rl1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K4rl14C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS5SMMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8max_specC69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR?model_ok_but_vmC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8cle_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:saves_keepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS7ascii_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_app_asciiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS9xinv_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027PnAdStr4PQAS8ck_add_rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CBmodel_but_vm_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3ADVC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4CRa0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS7dphi_geC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsQ2k_concC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<ad_vsCk_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5PBADVC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsQ2v_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ2kC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsCkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ2vC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4prepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01889PnAdVKitC7PNADVKC>utf8_valid_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5AFTERC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8INSVIEWCC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>ad_vsIkS2_concC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>ad_vsIvS2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>ad_vsIkL2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP>ad_vsIvL2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIkS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIvS2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIkL2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<KS_ad_vsIvL2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS9VIEW_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS3INSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsQ1k_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsQ1v_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ1kC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsQ1vC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8VIEW_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8xinv_frzC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5VIEW0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS5xinv0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7view_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsEd2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS:entry_postC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS8view_okEC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4ea_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ea_tagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ea_bsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_strC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout9ne_stringC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_modC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z7add_modC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8pre_vstrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_strC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<ad_vsR1_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3cfgC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsEd2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8TAG_NONEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS6ENC_HSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsR1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP=ad_vsEk2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9eargs_keyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout6ne_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM:hdr_str_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7hdr_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pre_keyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8step_keyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP<ad_vsR2_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP;KS_ad_vsEk2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01928PnAdSVsP7PQADVSP:KS_ad_vsR2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;exists_lastC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8args_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV7pre_strC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lc69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS;u64_at_funcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5zsizeC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif3sig00I47Corelib4Init6Specif4sigT00C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8dphi_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV6ts_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8step_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01927PnAdSVs6PNADVS4MAINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189PnLayoutQ;qa_v_stringC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV=v_string_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8step_strC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01026PnVisN3PNV8view_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib7Mh_01026PnVisN3PNV5VIS_HC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00". Local Ltac lia := L5FastLia.plia.

Module PNADVS.
Import PMS.
Import NEM.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation AQ := PnLayoutQS.QADDR_S.
Abbreviation AE := NemLayoutS.NEADDR_S.
Abbreviation kstr_at := (PQM.kstr_at RSEGS PMSP.T3).
Abbreviation adaptor_at := (PQM.adaptor_at RSEGS AD PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).
Abbreviation ec_state := (NEM.ec_state RSEGS AD).
Abbreviation err_ok := (PQST.err_ok RSEGS AD AQ).
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Lemma u64_at_func (M : word -> option byte) a v v' : L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M a v' -> 0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) [] (Mh_0192_blobs1.kr_b_182 ())). Qed.
Lemma ascii_1 ch : 0 <= ch < 128 -> ascii [ch].
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) [] (Mh_0192_blobs1.kr_b_183 ())). Qed.

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
(* [comment removed for export] *)
Hypothesis VSE : NECS.v_string_spec RSEGS AD AQ AE L HI NESK.PME.
Hypothesis VKE : NECS.v_key_spec RSEGS AD AQ AE L HI NESK.PME.
Abbreviation ae_at := (NEM.ae_at RSEGS AD AE L PMSP.T3 PMSP.T4 (qa_vp_adaptor AQ)).
Abbreviation enc_at := (NEM.enc_at RSEGS AE L PMSP.T3 PMSP.T4).
Abbreviation sink_at := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 NESK.PME).

(* [comment removed for export] *)
Definition kclr (x : PM.vstr) : PM.vstr := match x with PM.VShort _ => PM.VShort 0 | PM.VLong cc _ qq => PM.VLong cc 0 qq end.
Lemma kclr_size x : PM.vs_size (kclr x) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_184 ())). Qed.
Lemma kclr_data o x : PM.vs_data o (kclr x) = PM.vs_data o x.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_185 ())). Qed.
Lemma kclr_ok x g : PQM.ks_ok PQM.SMK x g -> PQM.ks_ok PQM.SMK (kclr x) g.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_186 ())). Qed.
Lemma kclr_pot lvX bX kX kx kgx kbx gx : PQM.pot_adaptor L (PQM.AST lvX bX kX (kclr kx) kgx kbx gx) = PQM.pot_adaptor L (PQM.AST lvX bX kX kx kgx kbx gx).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_187 ())). Qed.
Lemma kclr_own lvX bX kX kx kgx kbx gx : PQM.aown (PQM.AST lvX bX kX (kclr kx) kgx kbx gx) = PQM.aown (PQM.AST lvX bX kX kx kgx kbx gx).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_188 ())). Qed.

(* [comment removed for export] *)
Lemma pot_ae_split a kbb1 en1 sk1 :
  pot_ae L (AEST a kbb1 en1 sk1) = PM.credit_add (PQM.pot_adaptor L a) (PM.credit_add (pot_estack L (en_k en1)) (NESK.sink_pot NESK.PME (NESK.sk_c sk1))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_189 ())). Qed.
Lemma enc_pot_nonneg M o en1 sk1 : 0 <= en_k en1 <= EKMAX -> sink_at M o sk1 ->
  0 <= fst (PM.credit_add (pot_estack L (en_k en1)) (NESK.sink_pot NESK.PME (NESK.sk_c sk1)))
  /\ 0 <= snd (PM.credit_add (pot_estack L (en_k en1)) (NESK.sink_pot NESK.PME (NESK.sk_c sk1))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_190 ())). Qed.

Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (cr0 : credit).
Variables (S r oa ov osk oec cat : Z) (bf ef : bool).
Variables (lv0 : list PQM.alvl) (c : PQM.alvl) (b k : Z) (key : PM.vstr) (kg : Z) (kb : PM.vstr) (kbg : Z) (kbb : list Z) (en : enc) (sk : NESK.sink).
(* [comment removed for export] *)
Variables (vp vd vn vt : Z) (vbs : list Z).
Let lv : list PQM.alvl := lv0 ++ [c].
Let ast : PQM.ast := PQM.AST lv b k key kg kb kbg.
Let st : aest := AEST ast kbb en sk.
Let stW (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z) : PQM.ast := PQM.AST lv b k kx kgx kbx gx.
(* [comment removed for export] *)
Let ESO : list (Z * Z) := enc_own en ++ NESK.sink_own sk.
Let LBXe : list (Z * Z) := ESO ++ LBX.
Let n : Z := Z.of_nat (length lv0) + 1.
Let e0 : Z := b + 24 * n.
Hypothesis HH0 : hi_heap HI (aeown st ++ LBX) cr0 M0 (m_vmmaps model0).
Hypothesis MOK0 : PMSP.model_ok model0.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 28672.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 oa.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 vp.
Hypothesis Hvp : S <= vp /\ vp + 16 <= oa.
Hypothesis VP : L5.u64_at RSEGS M0 vp vd.
Hypothesis VN : L5.u64_at RSEGS M0 (vp + 8) vn.
Hypothesis Hvn : 0 <= vn < 2 ^ 29.   (* [comment removed for export] *)
Hypothesis VD : L5.defined M0 vd vn.
Hypothesis VW : vn = 0 \/ PGS.in_blk LBX vd vn \/ (S <= vd /\ vd + vn <= oa /\ 4096 <= vd).
Hypothesis VR : 0 <= vd /\ vd + vn <= 2 ^ 47.
Hypothesis A12 : getr R0 (reg 12) = Z_to_bv 64 vt.
Hypothesis Hvt : vt = TAG_NONE \/ vt = TAG_ENANO.
Hypothesis A14 : getr R0 (reg 14) = Z_to_bv 64 oec.
Hypothesis VBS : L5.bytes_at RSEGS M0 vd vbs.
Hypothesis VLEN : Z.of_nat (length vbs) = vn.
Hypothesis VU8 : utf8_valid vbs = true.
Hypothesis VBOK : bytes_ok vbs.
Hypothesis VR8 : vt = TAG_ENANO -> vn <= 31.
Hypothesis Ho1 : S <= oa.
Hypothesis Ho2 : oa + PQM.ASIZE <= hl_sptop L.
Hypothesis Ho3 : oa mod 8 = 0.
Hypothesis Hov1 : S <= ov.
Hypothesis Hov2 : ov + 56 <= hl_sptop L.
Hypothesis Hov3 : oa + PQM.ASIZE <= ov.
Hypothesis Hovm : ov mod 8 = 0.
Hypothesis Hk1 : S <= osk.
Hypothesis Hk2 : osk + 24 <= hl_sptop L.
Hypothesis Hk3 : osk mod 8 = 0.
Hypothesis Hvk : ov + 56 <= osk.
Hypothesis He1 : S <= oec.
Hypothesis He2 : oec + 16 <= hl_sptop L.
Hypothesis He3 : oec mod 8 = 0.
Hypothesis He4 : oec + 16 <= oa.
Hypothesis AA0 : ae_at M0 oa ov osk st.
Hypothesis AOK0 : ae_ok st.
Hypothesis ECS0 : ec_state M0 oec bf cat.
Hypothesis BASE0 : PMST.base_ok RSEGS AD M0.
Hypothesis ERR0 : err_ok M0 ef.
Hypothesis PRE0 : PQM.kbsize ast + vn + 4 <= PQM.SMB.
Let dphi : Z := if vt =? TAG_ENANO then Z.max (vn + 5) 15 else vn + 5.
Hypothesis PREZ : NESK.sk_z sk + dphi <= NESK.SMZ.
Hypothesis CR0 : PMSP.credit_le (pot_ae L st) cr0.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (st' : aest) (b' e' : bool) (cr' : credit),
  regs_preserved R0 R' -> ae_at M' oa ov osk st' -> ae_ok st' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS AD M' -> err_ok M' e' ->
  (bf = true -> b' = true) -> (ef = true -> e' = true) ->
  (nlv st' = nlv st /\ kbsize st' <= kbsize st + (vn + 4) /\ phi st' <= phi st + dphi /\ esize st' = esize st /\ edepth st' = edepth st /\ (b' = bf \/ vt = TAG_ENANO)) ->
  L5C.hpres L LBX S 28672 (ae_W AD oa ov osk oec) M0 M' ->
  PMSP.credit_keep cr0 cr' (pot_ae L st) (pot_ae L st') ->
  model_but_vm model0 model' -> hi_heap HI (aeown st' ++ LBX) cr' M' (m_vmmaps model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

(* [comment removed for export] *)
Lemma aeown_app : aeown st ++ LBX = PQM.aown ast ++ LBXe.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_191 ())). Qed.
Lemma BRXe : PMFR.brange L LBXe.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_192 ())). Qed.
Lemma BRX : PMFR.brange L LBX.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_193 ())). Qed.
Lemma VT0 : L5.u64_at RSEGS M0 ov (ne_vt AE).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_194 ())). Qed.
Let CX : PNADVK.ctx_ok L M0 K LBX S oa ov := conj K0 (conj STK0 (conj Ho1 (conj Ho2 (conj Ho3 (conj Hov1 (conj Hov2 (conj Hov3 (conj VT0 (conj BASE0 BRX))))))))).
Let CXe : PNADVK.ctx_ok L M0 K LBXe S oa ov := conj K0 (conj STK0 (conj Ho1 (conj Ho2 (conj Ho3 (conj Hov1 (conj Hov2 (conj Hov3 (conj VT0 (conj BASE0 BRXe))))))))).
Let CXO : S <= osk /\ osk + 24 <= hl_sptop L /\ osk mod 8 = 0 /\ S <= oec /\ oec + 16 <= hl_sptop L /\ oec mod 8 = 0 /\ oec + 16 <= oa /\ ov + 56 <= osk /\ ov mod 8 = 0 :=
  conj Hk1 (conj Hk2 (conj Hk3 (conj He1 (conj He2 (conj He3 (conj He4 (conj Hvk Hovm))))))).
Abbreviation cm := (PNADVK.cm L M0 LBX S oa ov osk oec).
Abbreviation cme := (PNADVK.cm L M0 LBXe S oa ov osk oec).
Abbreviation world := (PNADVK.world ov).
(* [comment removed for export] *)
Let KIT_frame0 := PNADVK.frame0 L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kcm_hpres := PNADVK.cm_hpres L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let Kcm0 := PNADVK.cm0 L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let Kcm_frz := PNADVK.cm_frz L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX.
Let Kworld0 := PNADVK.world0 L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kworld_frz := PNADVK.world_frz L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kworld_img := PNADVK.world_img L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kworld_vis := PNADVK.world_vis L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kad_split := PNADVK.ad_split L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Kad_join := PNADVK.ad_join L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KHDR_keep := PNADVK.HDR_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KKEY_keep := PNADVK.KEY_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KKB_keep := PNADVK.KB_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KLV_keep := PNADVK.LV_keep L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let KLV_set_last := PNADVK.LV_set_last L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Ktop_cells := PNADVK.top_cells L HI LY HIok OPN OPD M0 K LBX S oa ov CX.
Let Ecm0 := PNADVK.cm0 L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let Ecm_frz := PNADVK.cm_frz L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EPBCALL := PNADVK.PBCALL L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EINSKB := PNADVK.INSKB L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let INSCC := PQADJNSC.ins_ok L HI LY HIok OPN OPD.   (* [comment removed for export] *)
Let Eafter_strcall := PNADVK.after_strcall L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let Eperm_kb := PNADVK.perm_kb L HI LY HIok OPN OPD M0 K LBXe S oa ov CXe.
Let Epot_parts := PNADVK.pot_parts L HI LY HIok OPN OPD M0 K LBXe S oa ov CXe.
Let Estrcall_blocks := PNADVKC.strcall_blocks L HI LY HIok OPN OPD M0 K LBXe S oa ov CXe.
Let Kheap_perm := PNADVK.heap_perm L HI HIok.
Let EPBKEY := PNADVKC.PBKEYC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EPBCALLC := PNADVKC.PBCALLC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let EINSKBC := PNADVKC.INSKBC L HI LY HIok OPN OPD M0 K LBXe S oa ov osk oec CXe.
Let KENC_SLOT := PNADEC.ENC_SLOT L HI LY HIok OPN OPD M0 K LBX S oa ov osk oec CX CXO.
Let KENC_KEY := PNADEC.ENC_KEY L HI LY HIok OPN OPD VKE M0 K LBX S oa ov osk oec CX CXO.
(* [comment removed for export] *)
Definition VIEW (M : word -> option byte) : Prop := L5.u64_at RSEGS M vp vd /\ L5.u64_at RSEGS M (vp + 8) vn /\ L5.defined M vd vn /\ L5.bytes_at RSEGS M vd vbs.
(* [comment removed for export] *)
Lemma AAa0 : adaptor_at M0 oa ov ast.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_195 ())). Qed.
Lemma HHe0 : hi_heap HI (PQM.aown ast ++ LBXe) cr0 M0 (m_vmmaps model0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_196 ())). Qed.
Lemma ENK : 0 <= en_k en <= EKMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_197 ())). Qed.
(* [comment removed for export] *)
Lemma CRa0 : PMSP.credit_le (PQM.pot_adaptor L ast) cr0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_198 ())). Qed.

Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (bv_unsigned (getr R0 (reg 1))) /\ L5.u64_at RSEGS M (S - 16) (bv_unsigned (getr R0 (reg 8)))
  /\ L5.u64_at RSEGS M (S - 24) (bv_unsigned (getr R0 (reg 9))) /\ L5.u64_at RSEGS M (S - 32) (bv_unsigned (getr R0 (reg 18))).
Definition kept0 (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Lemma saves_keep M1 M2 : L5C.agree_on M1 M2 (S - 32) 32 -> saves M1 -> saves M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_199 ())). Qed.
Lemma blk : 4096 <= b /\ (b + 24 * 2 ^ k <= 0x10000 \/ 0xfa000 <= b) /\ b + 24 * 2 ^ k <= hl_ceil L /\ 0 <= k <= 11 /\ n <= 2 ^ k /\ b mod 16 = 0 /\ 1 <= 2 ^ k <= 2048 /\ 1 <= n <= 1025.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_200 ())). Qed.
Lemma e_facts : e0 = b + 24 * n /\ 4096 + 24 <= e0 /\ e0 <= b + 24 * 2 ^ k /\ b + 24 * 2 ^ k + 28672 <= S /\ e0 mod 8 = 0 /\ (e0 <= 0x10000 \/ 0xfa000 <= e0 - 24).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_201 ())). Qed.
Lemma c_ok : PQM.alvl_ok c /\ PQM.lv_shape lv /\ (PQM.lv_t c = 1 -> PQM.lv_k c <> 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_202 ())). Qed.
(* [comment removed for export] *)
Lemma own_lv a : b <= a < b + 24 * 2 ^ k -> a < hl_ceil L /\ (a < hl_img_lo L \/ hl_img_hi L <= a) /\ ~ in_block LBXe a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_203 ())). Qed.
Lemma in_block_e a : ~ in_block LBXe a -> ~ in_block LBX a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_204 ())). Qed.
(* [comment removed for export] *)
Lemma cm_of_cme M : cme M -> cm M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_205 ())). Qed.
Lemma cs_restore (R1 R2 : bvmap 5 word) (KS : list nat) :
  kept0 R1 -> (forall x, In x KS -> getr R2 (reg x) = getr R1 (reg x)) -> forallb (fun x => existsb (Nat.eqb x) KS) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat = true ->
  getr R2 (reg 2) = Z_to_bv 64 S -> getr R2 (reg 8) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 8))) -> getr R2 (reg 9) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 9))) ->
  getr R2 (reg 18) = Z_to_bv 64 (bv_unsigned (getr R0 (reg 18))) ->
  forall x, In x PMK.cs_all -> getr R2 (reg x) = getr R0 (reg x).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_206 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xinv (M : word -> option byte) (kbx : PM.vstr) (kbb1 : list Z) (en1 : enc) (sk1 : NESK.sink) (b1 e1 : bool) : Prop :=
  kcontent RSEGS M (oa + PQM.AOFF_KB) kbx kbb1 /\ utf8_valid kbb1 = true /\ enc_at M ov osk en1 /\ sink_at M osk sk1
  /\ ec_state M oec b1 cat /\ err_ok M e1 /\ (bf = true -> b1 = true) /\ (ef = true -> e1 = true)
  /\ en_n en1 = en_n en /\ en_depth en1 = en_depth en /\ (b1 = bf \/ vt = TAG_ENANO).
Lemma xinv0 : xinv M0 kb kbb en sk bf ef.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_207 ())). Qed.
(* [comment removed for export] *)
Lemma lv_apart M VM cr kx kgx kbx gx kbb1 en1 sk1 a :
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr M VM -> b <= a < b + 24 * 2 ^ k ->
  ~ in_block (PM.vs_own kx ++ PM.vs_own kbx ++ (enc_own en1 ++ NESK.sink_own sk1) ++ LBX) a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_208 ())). Qed.
(* [comment removed for export] *)
Lemma blocks_hi M VM cr kx kgx kbx gx kbb1 en1 sk1 B m :
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr M VM -> In (B, m) (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) ->
  4096 <= B /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B) /\ B + m <= hl_ceil L.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_209 ())). Qed.

(* [comment removed for export] *)
Lemma err_ok_frz M1 M2 (P : Z -> Prop) e1 :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> a < hl_img_lo L \/ hl_img_hi L <= a) -> err_ok M1 e1 -> err_ok M2 e1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_210 ())). Qed.

(* [comment removed for export] *)
Lemma xinv_frz M1 M2 (P : Z -> Prop) kx kgx kbx gx kbb1 en1 sk1 b1 e1 cr VM :
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr M1 VM -> adaptor_at M1 oa ov (stW kx kgx kbx gx) ->
  mem_grows M1 M2 -> (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) ->
  (forall a, P a -> S - 28672 <= a < S \/ oa + 24 <= a < oa + 48 \/ b <= a < b + 24 * 2 ^ k \/ in_block (PM.vs_own kx) a) ->
  xinv M1 kbx kbb1 en1 sk1 b1 e1 -> xinv M2 kbx kbb1 en1 sk1 b1 e1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_211 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FIN (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (st' : aest) (b1 e1 : bool) (cr1 : credit) :
  getr R1 (reg 1) = Z_to_bv 64 r -> (forall x, In x PMK.cs_all -> getr R1 (reg x) = getr R0 (reg x)) ->
  ae_at M1 oa ov osk st' -> ae_ok st' -> ec_state M1 oec b1 cat -> PMST.base_ok RSEGS AD M1 -> err_ok M1 e1 ->
  (bf = true -> b1 = true) -> (ef = true -> e1 = true) ->
  (nlv st' = nlv st /\ kbsize st' <= kbsize st + (vn + 4) /\ phi st' <= phi st + dphi /\ esize st' = esize st /\ edepth st' = edepth st /\ (b1 = bf \/ vt = TAG_ENANO)) ->
  cm M1 -> PMSP.credit_keep cr0 cr1 (pot_ae L st) (pot_ae L st') -> model_but_vm model0 model1 ->
  hi_heap HI (aeown st' ++ LBX) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3badc M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_212 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ADV (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z)
      (kbb1 : list Z) (en1 : enc) (sk1 : NESK.sink) (b1 e1 : bool) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 32) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 vp -> kept0 R1 ->
  saves M1 -> cm M1 -> world M1 -> adaptor_at M1 oa ov (stW kx kgx kbx gx) -> PQM.ks_ok PQM.SMK kx kgx -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx <= PM.vs_size kb + (vn + 4) ->
  xinv M1 kbx kbb1 en1 sk1 b1 e1 -> NESK.sk_z sk1 + PM.vs_size kbx <= NESK.sk_z sk + PM.vs_size kb + dphi ->
  PMSP.credit_keep cr0 cr1 (pot_ae L st) (pot_ae L (AEST (stW kx kgx kbx gx) kbb1 en1 sk1)) -> model_but_vm model0 model1 ->
  hi_heap HI (aeown (AEST (stW kx kgx kbx gx) kbb1 en1 sk1) ++ LBX) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x3ba98 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_213 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aeown_appW a kbb1 : aeown (AEST a kbb1 en sk) ++ LBX = PQM.aown a ++ LBXe.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_214 ())). Qed.
(* [comment removed for export] *)
Lemma xinv_call M Mq kbx kbb1 kbx' kbb' b1 e1 (lo wlo : Z) :
  lo <= S -> (wlo = oa + 24 \/ wlo = oa + 48) ->
  (forall a m, lo <= a -> a + m <= 2 ^ 64 -> (a + m <= wlo \/ wlo + 24 <= a) -> L5C.agree_on M Mq a m) ->
  (forall B m, In (B, m) LBXe -> L5C.agree_on M Mq B m) ->
  (forall e, err_ok M e -> err_ok Mq e) ->
  kcontent RSEGS Mq (oa + PQM.AOFF_KB) kbx' kbb' -> utf8_valid kbb' = true ->
  xinv M kbx kbb1 en sk b1 e1 -> xinv Mq kbx' kbb' en sk b1 e1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_215 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma long_facts M o cc mm qq LL cr VM :
  kstr_at M o (PM.VLong cc mm qq) -> In (qq, cc) LL -> hi_heap HI LL cr M VM ->
  L5.u8_at RSEGS M o ((cc + 1) mod 256) /\ 0 <= (cc + 1) mod 256 <= 255 /\ Z.testbit ((cc + 1) mod 256) 0 = true /\ L5.u64_at RSEGS M (o + 8) mm /\ L5.u64_at RSEGS M (o + 16) qq
  /\ 0 <= mm < cc /\ 26 <= cc <= PQM.KCAP /\ 4096 <= qq /\ qq + cc <= hl_ceil L /\ (qq + cc <= 0x10000 \/ 0xfa000 <= qq) /\ L5.defined M qq cc /\ L5.writable RSEGS M qq 1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_216 ())). Qed.
Lemma short_facts M o mm : kstr_at M o (PM.VShort mm) -> L5.u8_at RSEGS M o (2 * mm) /\ 0 <= mm <= 22 /\ 0 <= Z.land ((2 * mm) mod 2 ^ 64) 1 <= 0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_217 ())). Qed.
(* [comment removed for export] *)
Lemma prep (M : word -> option byte) (kx : PM.vstr) (kgx : Z) (kbx : PM.vstr) (gx : Z) :
  cm M -> adaptor_at M oa ov (stW kx kgx kbx gx) ->
  L5.writable RSEGS M (S - 32) 32 /\ L5.writable RSEGS M (oa + 24) 72 /\ L5.writable RSEGS M (e0 - 24) 24 /\ L5.u64_at RSEGS M (oa + 80) e0
  /\ L5.u32_at RSEGS M (e0 - 24) (PQM.lv_t c) /\ L5.u32_at RSEGS M (e0 - 20) (PQM.lv_k c) /\ L5.u32_at RSEGS M (e0 - 16) (PQM.lv_eo c) /\ L5.defined M (e0 - 8) 8
  /\ L5.u64_at RSEGS M (oa + 16) ov /\ PNADVK.KEY oa M kx /\ PNADVK.KB oa M kbx.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_218 ())). Qed.
Lemma cme_cm M : cme M -> cm M.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_219 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vw_facts : vn = 0 \/ (vd + vn < 2 ^ 47 /\
  ((exists B m, In (B, m) LBX /\ B <= vd /\ vd + vn <= B + m /\ 4096 <= B /\ B + m <= hl_ceil L /\ (B + m <= hl_img_lo L \/ hl_img_hi L <= B)) \/ (S <= vd /\ vd + vn <= oa /\ 4096 <= vd))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_220 ())). Qed.
Lemma VIEW0 : VIEW M0.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_221 ())). Qed.
Lemma VIEW_keep M1 M2 : VIEW M1 -> L5C.agree_on M1 M2 vp 16 -> L5C.agree_on M1 M2 vd vn -> VIEW M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_222 ())). Qed.
(* [comment removed for export] *)
Lemma VIEW_frz M1 M2 (P : Z -> Prop) :
  (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i)) -> (forall a, P a -> S - 28672 <= a < S) -> VIEW M1 -> VIEW M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_223 ())). Qed.
(* [comment removed for export] *)
Lemma VIEW_call M1 M2 (lo wlo : Z) :
  lo <= S -> oa + 24 <= wlo ->
  (forall a m, lo <= a -> a + m <= 2 ^ 64 -> (a + m <= wlo \/ wlo + 24 <= a) -> L5C.agree_on M1 M2 a m) ->
  (forall B m, In (B, m) LBX -> L5C.agree_on M1 M2 B m) -> VIEW M1 -> VIEW M2.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_224 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma INSVIEWC (sp' : Z) (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (kb1 : PM.vstr) (g1 : Z) (kbb1 : list Z) (cr : credit) (ra : Z) :
  S - 4096 <= sp' -> sp' <= S -> sp' mod 16 = 0 ->
  getr R (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R (reg 2) = Z_to_bv 64 sp' -> getr R (reg 3) = Z_to_bv 64 (pa_gp AD) -> getr R (reg 4) = Z_to_bv 64 (pa_tp AD) ->
  getr R (reg 10) = Z_to_bv 64 (oa + 48) -> getr R (reg 11) = Z_to_bv 64 (PM.vs_data (oa + 48) kb1 + PM.vs_size kb1) ->
  getr R (reg 12) = Z_to_bv 64 vd -> getr R (reg 13) = Z_to_bv 64 (vd + vn) -> getr R (reg 14) = Z_to_bv 64 vn ->
  PM.vs_size kb1 + vn <= PQM.SMB ->
  cme M -> world M -> VIEW M -> adaptor_at M oa ov (stW key kg kb1 g1) -> kcontent RSEGS M (oa + 48) kb1 kbb1 -> PQM.ks_ok PQM.SMB kb1 g1 ->
  PMSP.credit_le (PQM.pot_adaptor L (stW key kg kb1 g1)) cr -> PMSP.model_ok model ->
  hi_heap HI (PQM.aown (stW key kg kb1 g1) ++ LBXe) cr M (m_vmmaps model) ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (kb2 : PM.vstr) (g2 : Z) (cr' : credit),
      regs_preserved R R' -> cme M' -> world M' ->
      (forall a m, sp' <= a -> a + m <= 2 ^ 64 -> (a + m <= oa + 48 \/ oa + 72 <= a) -> L5C.agree_on M M' a m) ->
      (forall B m, In (B, m) (PQM.lvec_own b k ++ PM.vs_own key ++ LBXe) -> L5C.agree_on M M' B m) -> (forall e, err_ok M e -> err_ok M' e) ->
      adaptor_at M' oa ov (stW key kg kb2 g2) -> kcontent RSEGS M' (oa + 48) kb2 (kbb1 ++ vbs) -> PQM.ks_ok PQM.SMB kb2 g2 -> PM.vs_size kb2 = PM.vs_size kb1 + vn ->
      PMSP.credit_keep cr cr' (PQM.pot_adaptor L (stW key kg kb1 g1)) (PQM.pot_adaptor L (stW key kg kb2 g2)) ->
      model_but_vm model model' -> hi_heap HI (PQM.aown (stW key kg kb2 g2) ++ LBXe) cr' M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' ra M' model') K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x3e908 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_225 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dphi_ge : vn + 4 <= dphi.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_226 ())). Qed.

(* [comment removed for export] *)
Lemma PBADV (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kbx : PM.vstr) (gx : Z) (kbb1 : list Z) (cr1 : credit) (ch : Z) :
  getr R1 (reg 1) = Z_to_bv 64 0x3ba98 -> getr R1 (reg 2) = Z_to_bv 64 (S - 32) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 vp ->
  getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 128 -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW key kg kbx gx) -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx + 1 <= PM.vs_size kb + vn + 4 ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW key kg kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW key kg kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x66444 M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_227 ())). Qed.

(* [comment removed for export] *)
Lemma AFTER (isK : bool) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kbx : PM.vstr) (gx : Z) (kbb1 : list Z) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 32) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 vp -> getr R1 (reg 18) = Z_to_bv 64 (oa + 48) -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> adaptor_at M1 oa ov (stW key kg kbx gx) -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx + (if isK then 2 else 1) <= PM.vs_size kb + vn + 4 ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW key kg kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW key kg kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if isK then 0x3ba80 else 0x3ba54) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_228 ())). Qed.

(* [comment removed for export] *)
Lemma INS (isK : bool) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kbx : PM.vstr) (gx : Z) (kbb1 : list Z) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 32) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 vp -> getr R1 (reg 18) = Z_to_bv 64 (oa + 48) -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> VIEW M1 -> adaptor_at M1 oa ov (stW key kg kbx gx) -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx + (if isK then 2 else 1) <= PM.vs_size kb + 4 ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW key kg kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW key kg kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if isK then 0x3b9dc else 0x3b998) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_229 ())). Qed.

(* [comment removed for export] *)
Lemma Q1 (isK : bool) (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (kbx : PM.vstr) (gx : Z) (kbb1 : list Z) (cr1 : credit) :
  getr R1 (reg 2) = Z_to_bv 64 (S - 32) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 vp -> (isK = false -> getr R1 (reg 18) = Z_to_bv 64 (oa + 48)) -> kept0 R1 ->
  saves M1 -> cme M1 -> world M1 -> VIEW M1 -> adaptor_at M1 oa ov (stW key kg kbx gx) -> PQM.ks_ok PQM.SMB kbx gx -> PM.vs_size kbx <= PM.vs_size kb + 1 ->
  xinv M1 kbx kbb1 en sk bf ef ->
  PMSP.credit_keep cr0 cr1 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW key kg kbx gx)) -> model_but_vm model0 model1 ->
  hi_heap HI (PQM.aown (stW key kg kbx gx) ++ LBXe) cr1 M1 (m_vmmaps model1) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (if isK then 0x3b9cc else 0x3b98c) M1 model1) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_230 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_post (M1 : word -> option byte) :
  mem_grows M0 M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 32 <= i < S - 32 + 32) -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)) ->
  cme M1 /\ cm M1 /\ world M1 /\ VIEW M1 /\ adaptor_at M1 oa ov ast /\ xinv M1 kb kbb en sk bf ef /\ (forall a, S - 32 <= a < S - 32 + 32 -> PMK.cwr L (aeown st ++ LBX) a).
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_231 ())). Qed.

(* [comment removed for export] *)
Lemma view_okE (M1 : word -> option byte) (a : PQM.ast) :
  VIEW M1 -> NECS.view_ok RSEGS M1 (S - 32) ov (PQM.aown a ++ LBX) vp vd vn.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_232 ())). Qed.

(* [comment removed for export] *)
Lemma EDV : PQM.lv_eo c = 1 -> PQM.lv_t c = 0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b934 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_233 ())). Qed.

(* [comment removed for export] *)
Lemma EDK : PQM.lv_eo c = 0 -> PQM.lv_t c = 0 -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b934 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_234 ())). Qed.

(* [comment removed for export] *)
Lemma EPB (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (KS : list nat) (ra ch : Z) (hasS2 : bool) :
  mem_grows M0 M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ (S - 32 <= i < S - 32 + 32) -> M1 (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)) ->
  msteps RSEGS (mst fx0 R0 0x3b934 M0) (mst fx1 R1 0x66444 M1) ->
  (forall y, In y KS -> getr R1 (reg y) = getr R0 (reg y)) -> forallb (fun y => existsb (Nat.eqb y) KS) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat = true ->
  getr R1 (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra -> getr R1 (reg 2) = Z_to_bv 64 (S - 32) -> getr R1 (reg 8) = Z_to_bv 64 oa -> getr R1 (reg 9) = Z_to_bv 64 vp ->
  getr R1 (reg 10) = Z_to_bv 64 (oa + 48) -> getr R1 (reg 11) = Z_to_bv 64 ch -> 0 <= ch < 128 -> (hasS2 = true -> getr R1 (reg 18) = Z_to_bv 64 (oa + 48)) -> saves M1 ->
  (forall (fx3 : FPState) (R3 : bvmap 5 word) (M3 : word -> option byte) (model3 : Model) (kb2 : PM.vstr) (g2 : Z) (cr3 : credit),
      getr R3 (reg 2) = Z_to_bv 64 (S - 32) -> getr R3 (reg 8) = Z_to_bv 64 oa -> getr R3 (reg 9) = Z_to_bv 64 vp -> (hasS2 = true -> getr R3 (reg 18) = Z_to_bv 64 (oa + 48)) -> kept0 R3 ->
      saves M3 -> cme M3 -> world M3 -> VIEW M3 -> adaptor_at M3 oa ov (stW key kg kb2 g2) -> PQM.ks_ok PQM.SMB kb2 g2 -> PM.vs_size kb2 = PM.vs_size kb + 1 ->
      xinv M3 kb2 (kbb ++ [ch]) en sk bf ef ->
      PMSP.credit_keep cr0 cr3 (PQM.pot_adaptor L ast) (PQM.pot_adaptor L (stW key kg kb2 g2)) -> model_but_vm model0 model3 ->
      hi_heap HI (PQM.aown (stW key kg kb2 g2) ++ LBXe) cr3 M3 (m_vmmaps model3) ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 ra M3 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b934 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_235 ())). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENV : nat -> Z := fun j => match j with 2%nat => S | 36%nat => oa | 37%nat => e0 | 38%nat => ov | 55%nat => vp | _ => 0 end.
Definition ENVc (cnt : Z) : nat -> Z := fun j => match j with 2%nat => S | 36%nat => oa | 37%nat => e0 | 38%nat => ov | 39%nat => cnt | 55%nat => vp | _ => 0 end.

Lemma MAIN : srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx0 R0 0x3b934 M0 model0) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_236 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem string_ok : PNV.v_string_spec RSEGS AD AQ AE L HI.
Proof.
ltac2:(KReplay.run1 (kr_t_PnAdSVs ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_237 ())). Qed.

End WithHeap.
End PNADVS.

End PnAdSVs.
Module PnSEncBsrP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncBsrP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF1<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF16cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF13kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brF1_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF29regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF2C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF2<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF26cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF23ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brF2_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF49regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF4C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF4<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF46cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF43ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brF4_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brF8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF86cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrF83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brF8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brF16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrF163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brF16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8aC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8a3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE8a_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8bC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE8b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8cC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8c3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE8c_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8dC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8d3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE8d_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8eC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e6cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8e3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE8e_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE8nC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE8n3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE8n_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brW16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brW16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brJ16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brJ16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brE32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE326cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrE323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brE32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brW32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrW323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brW32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brJ32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrJ323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brJ32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brTC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrT3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9KS_brT_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brL0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brL0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brL1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrL13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brL1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9KS_brB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brNC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrN3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9KS_brN_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brEC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP4PbrE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9KS_brE_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brV0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brV0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brV1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV13NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:KS_brV1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP5PbrV16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brV1wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP;KS_brV1w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6PbrV1w6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSENBRP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_238 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_239 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_240 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_241 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_242 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_243 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_244 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_245 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_246 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_247 ())). Qed.
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
Module PbrF1 := BndP_Ns_042.LibSegNs_brF1.
Definition KS_brF1 : list nat := Eval vm_compute in (BG.kept_list 60 PbrF1.regs0 PbrF1.regs_out0).
Lemma KS_brF1_ok : BG.kept_ok 60 PbrF1.regs0 PbrF1.regs_out0 KS_brF1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_248 ())). Qed.
Lemma brF1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brF1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265904
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_249 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrF2 := BndP_Ns_042.LibSegNs_brF2.
Definition KS_brF2 : list nat := Eval vm_compute in (BG.kept_list 60 PbrF2.regs0 PbrF2.regs_out0).
Lemma KS_brF2_ok : BG.kept_ok 60 PbrF2.regs0 PbrF2.regs_out0 KS_brF2 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_250 ())). Qed.
Lemma brF2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 2 <= (V 34%nat) <= 2 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brF2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265904
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_251 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrF4 := BndP_Ns_042.LibSegNs_brF4.
Definition KS_brF4 : list nat := Eval vm_compute in (BG.kept_list 60 PbrF4.regs0 PbrF4.regs_out0).
Lemma KS_brF4_ok : BG.kept_ok 60 PbrF4.regs0 PbrF4.regs_out0 KS_brF4 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_252 ())). Qed.
Lemma brF4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 4 <= (V 34%nat) <= 4 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brF4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265904
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_253 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrF8 := BndP_Ns_042.LibSegNs_brF8.
Definition KS_brF8 : list nat := Eval vm_compute in (BG.kept_list 60 PbrF8.regs0 PbrF8.regs_out0).
Lemma KS_brF8_ok : BG.kept_ok 60 PbrF8.regs0 PbrF8.regs_out0 KS_brF8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_254 ())). Qed.
Lemma brF8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 8 <= (V 34%nat) <= 8 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brF8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265904
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 8
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_255 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrF16 := BndP_Ns_042.LibSegNs_brF16.
Definition KS_brF16 : list nat := Eval vm_compute in (BG.kept_list 60 PbrF16.regs0 PbrF16.regs_out0).
Lemma KS_brF16_ok : BG.kept_ok 60 PbrF16.regs0 PbrF16.regs_out0 KS_brF16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_256 ())). Qed.
Lemma brF16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 16 <= (V 34%nat) <= 16 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brF16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265904
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 16
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_257 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE8a := BndP_Ns_041.LibSegNs_brE8a.
Definition KS_brE8a : list nat := Eval vm_compute in (BG.kept_list 60 PbrE8a.regs0 PbrE8a.regs_out0).
Lemma KS_brE8a_ok : BG.kept_ok 60 PbrE8a.regs0 PbrE8a.regs_out0 KS_brE8a = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_258 ())). Qed.
Lemma brE8a_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 0 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE8a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_259 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE8b := BndP_Ns_041.LibSegNs_brE8b.
Definition KS_brE8b : list nat := Eval vm_compute in (BG.kept_list 60 PbrE8b.regs0 PbrE8b.regs_out0).
Lemma KS_brE8b_ok : BG.kept_ok 60 PbrE8b.regs0 PbrE8b.regs_out0 KS_brE8b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_260 ())). Qed.
Lemma brE8b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 3 <= (V 34%nat) <= 3 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE8b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 3
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_261 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE8c := BndP_Ns_041.LibSegNs_brE8c.
Definition KS_brE8c : list nat := Eval vm_compute in (BG.kept_list 60 PbrE8c.regs0 PbrE8c.regs_out0).
Lemma KS_brE8c_ok : BG.kept_ok 60 PbrE8c.regs0 PbrE8c.regs_out0 KS_brE8c = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_262 ())). Qed.
Lemma brE8c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 5 <= (V 34%nat) <= 7 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE8c -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_263 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE8d := BndP_Ns_041.LibSegNs_brE8d.
Definition KS_brE8d : list nat := Eval vm_compute in (BG.kept_list 60 PbrE8d.regs0 PbrE8d.regs_out0).
Lemma KS_brE8d_ok : BG.kept_ok 60 PbrE8d.regs0 PbrE8d.regs_out0 KS_brE8d = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_264 ())). Qed.
Lemma brE8d_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 9 <= (V 34%nat) <= 15 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE8d -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_265 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE8e := BndP_Ns_042.LibSegNs_brE8e.
Definition KS_brE8e : list nat := Eval vm_compute in (BG.kept_list 60 PbrE8e.regs0 PbrE8e.regs_out0).
Lemma KS_brE8e_ok : BG.kept_ok 60 PbrE8e.regs0 PbrE8e.regs_out0 KS_brE8e = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_266 ())). Qed.
Lemma brE8e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 17 <= (V 34%nat) <= 255 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE8e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266108
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_267 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE8n := BndP_Ns_042.LibSegNs_brE8n.
Definition KS_brE8n : list nat := Eval vm_compute in (BG.kept_list 60 PbrE8n.regs0 PbrE8n.regs_out0).
Lemma KS_brE8n_ok : BG.kept_ok 60 PbrE8n.regs0 PbrE8n.regs_out0 KS_brE8n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_268 ())). Qed.
Lemma brE8n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 34%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 49) <= bv_unsigned a < ((V 2%nat) - 49) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 49) <= i < ((V 2%nat) - 49) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40f7c M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE8n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265904
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_269 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE16 := BndP_Ns_041.LibSegNs_brE16.
Definition KS_brE16 : list nat := Eval vm_compute in (BG.kept_list 60 PbrE16.regs0 PbrE16.regs_out0).
Lemma KS_brE16_ok : BG.kept_ok 60 PbrE16.regs0 PbrE16.regs_out0 KS_brE16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_270 ())). Qed.
Lemma brE16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 256 <= (V 34%nat) <= 65535 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266144
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_271 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrW16 := BndP_Ns_043.LibSegNs_brW16.
Definition KS_brW16 : list nat := Eval vm_compute in (BG.kept_list 60 PbrW16.regs0 PbrW16.regs_out0).
Lemma KS_brW16_ok : BG.kept_ok 60 PbrW16.regs0 PbrW16.regs_out0 KS_brW16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_272 ())). Qed.
Lemma brW16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40fa0 M) (st fx' R' 0x41aec M')
        /\ (forall x, In x KS_brW16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266156
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_273 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrJ16 := BndP_Ns_042.LibSegNs_brJ16.
Definition KS_brJ16 : list nat := Eval vm_compute in (BG.kept_list 60 PbrJ16.regs0 PbrJ16.regs_out0).
Lemma KS_brJ16_ok : BG.kept_ok 60 PbrJ16.regs0 PbrJ16.regs_out0 KS_brJ16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_274 ())). Qed.
Lemma brJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 49) <= bv_unsigned a < ((V 2%nat) - 49) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 49) <= i < ((V 2%nat) - 49) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40fac M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brJ16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265920
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_275 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE32 := BndP_Ns_041.LibSegNs_brE32.
Definition KS_brE32 : list nat := Eval vm_compute in (BG.kept_list 60 PbrE32.regs0 PbrE32.regs_out0).
Lemma KS_brE32_ok : BG.kept_ok 60 PbrE32.regs0 PbrE32.regs_out0 KS_brE32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_276 ())). Qed.
Lemma brE32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 65536 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 64)) ->
  0 <= (bv_unsigned (getr R (reg 12))) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40e10 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brE32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266072
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)
        /\ getr R' (reg 18) = getr R (reg 12)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_277 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrW32 := BndP_Ns_043.LibSegNs_brW32.
Definition KS_brW32 : list nat := Eval vm_compute in (BG.kept_list 60 PbrW32.regs0 PbrW32.regs_out0).
Lemma KS_brW32_ok : BG.kept_ok 60 PbrW32.regs0 PbrW32.regs_out0 KS_brW32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_278 ())). Qed.
Lemma brW32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40f58 M) (st fx' R' 0x41b50 M')
        /\ (forall x, In x KS_brW32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 266084
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_279 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrJ32 := BndP_Ns_042.LibSegNs_brJ32.
Definition KS_brJ32 : list nat := Eval vm_compute in (BG.kept_list 60 PbrJ32.regs0 PbrJ32.regs_out0).
Lemma KS_brJ32_ok : BG.kept_ok 60 PbrJ32.regs0 PbrJ32.regs_out0 KS_brJ32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_280 ())). Qed.
Lemma brJ32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 49) <= bv_unsigned a < ((V 2%nat) - 49) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 49) <= i < ((V 2%nat) - 49) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40f64 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brJ32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265920
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_281 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrT := BndP_Ns_042.LibSegNs_brT.
Definition KS_brT : list nat := Eval vm_compute in (BG.kept_list 60 PbrT.regs0 PbrT.regs_out0).
Lemma KS_brT_ok : BG.kept_ok 60 PbrT.regs0 PbrT.regs_out0 KS_brT = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_282 ())). Qed.
Lemma brT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 49) <= bv_unsigned a < ((V 2%nat) - 49) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 49) <= i < ((V 2%nat) - 49) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40eb0 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265920
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_283 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrL0 := BndP_Ns_042.LibSegNs_brL0.
Definition KS_brL0 : list nat := Eval vm_compute in (BG.kept_list 60 PbrL0.regs0 PbrL0.regs_out0).
Lemma KS_brL0_ok : BG.kept_ok 60 PbrL0.regs0 PbrL0.regs_out0 KS_brL0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_284 ())). Qed.
Lemma brL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M ((V 11%nat) + 8) 0 ->
  (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40ec0 M) (st fx' R' 0x40eec M')
        /\ (forall x, In x KS_brL0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_285 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrL1 := BndP_Ns_042.LibSegNs_brL1.
Definition KS_brL1 : list nat := Eval vm_compute in (BG.kept_list 60 PbrL1.regs0 PbrL1.regs_out0).
Lemma KS_brL1_ok : BG.kept_ok 60 PbrL1.regs0 PbrL1.regs_out0 KS_brL1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_286 ())). Qed.
Lemma brL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 35%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40ec0 M) (st fx' R' 0x40ecc M')
        /\ (forall x, In x KS_brL1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_287 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrB := BndP_Ns_041.LibSegNs_brB.
Definition KS_brB : list nat := Eval vm_compute in (BG.kept_list 60 PbrB.regs0 PbrB.regs_out0).
Lemma KS_brB_ok : BG.kept_ok 60 PbrB.regs0 PbrB.regs_out0 KS_brB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_288 ())). Qed.
Lemma brB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 1 <= (V 36%nat) <= 140737488355327 -> L5.u8_at RSEGS M (V 36%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> 1 <= (V 38%nat) <= 536870911 -> (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 2%nat) - 64)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 49) <= bv_unsigned a < ((V 2%nat) - 49) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 49) <= i < ((V 2%nat) - 49) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40ecc M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_brB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265952
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 49)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_289 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrN := BndP_Ns_042.LibSegNs_brN.
Definition KS_brN : list nat := Eval vm_compute in (BG.kept_list 60 PbrN.regs0 PbrN.regs_out0).
Lemma KS_brN_ok : BG.kept_ok 60 PbrN.regs0 PbrN.regs_out0 KS_brN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_290 ())). Qed.
Lemma brN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1 <= (V 36%nat) <= 140737488355327 -> 2 <= (V 38%nat) <= 536870911 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40ee0 M) (st fx' R' 0x40ecc M')
        /\ (forall x, In x KS_brN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 38%nat) - 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_291 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrE := BndP_Ns_041.LibSegNs_brE.
Definition KS_brE : list nat := Eval vm_compute in (BG.kept_list 60 PbrE.regs0 PbrE.regs_out0).
Lemma KS_brE_ok : BG.kept_ok 60 PbrE.regs0 PbrE.regs_out0 KS_brE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_292 ())). Qed.
Lemma brE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 1 -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1 <= (V 36%nat) <= 140737488355327 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40ee0 M) (st fx' R' 0x40eec M')
        /\ (forall x, In x KS_brE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_293 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrV0 := BndP_Ns_042.LibSegNs_brV0.
Definition KS_brV0 : list nat := Eval vm_compute in (BG.kept_list 60 PbrV0.regs0 PbrV0.regs_out0).
Lemma KS_brV0_ok : BG.kept_ok 60 PbrV0.regs0 PbrV0.regs_out0 KS_brV0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_294 ())). Qed.
Lemma brV0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 57%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 58%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) -> 0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40eec M) (st fx' R' 0x40f24 M')
        /\ (forall x, In x KS_brV0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_295 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrV1 := BndP_Ns_043.LibSegNs_brV1.
Definition KS_brV1 : list nat := Eval vm_compute in (BG.kept_list 60 PbrV1.regs0 PbrV1.regs_out0).
Lemma KS_brV1_ok : BG.kept_ok 60 PbrV1.regs0 PbrV1.regs_out0 KS_brV1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_296 ())). Qed.
Lemma brV1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 57%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 58%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40eec M) (st fx' R' 0x40f24 M')
        /\ (forall x, In x KS_brV1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_297 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrV1w := BndP_Ns_043.LibSegNs_brV1w.
Definition KS_brV1w : list nat := Eval vm_compute in (BG.kept_list 60 PbrV1w.regs0 PbrV1w.regs_out0).
Lemma KS_brV1w_ok : BG.kept_ok 60 PbrV1w.regs0 PbrV1w.regs_out0 KS_brV1w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_298 ())). Qed.
Lemma brV1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 57%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 58%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 64) + 64 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 64) \/ ((V 2%nat) - 64) + 64 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40eec M) (st fx' R' 0x40f24 M')
        /\ (forall x, In x KS_brV1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsrP ()) [] (Mh_0192_blobs1.kr_b_299 ())). Qed.
(* [comment removed for export] *)

End PNSENBRP.

End PnSEncBsrP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require LeanFeed2. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034.
Module PnSEncBsr.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146.PnEncCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0192.PnSEncBsrP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_3fce0_41034.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncBsr () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indK47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega7Formula01C56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00C47Corelib4Init3Nat3subC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes7nat_indC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_geK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op204I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib7Numbers7BinNums8positive01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK8cells_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK9cred_sinkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4kctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR5CREDsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbc69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3CSLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List:in_app_iffC59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyK47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;brange_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR5ag_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4ea_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9step_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR8st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8brE_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR6CSLsubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR7ev_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_InC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8brB_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4cinvC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith6Zorder9Zle_0_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR7CSLcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR6tail_EC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8brN_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR3COKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brL0_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP9brL1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR4loopC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brL0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP7KS_brL1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8brT_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brJ16_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP:brJ32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR4at_LC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP6KS_brTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brJ16C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBsrP8PNSENBRP8KS_brJ32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS:eargs_bstrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8pre_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pot_encC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR@bytes_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBsr8PNSENBSR4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout;ne_bstr_rawC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS?v_bstr_raw_specC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01". Local Ltac lia := L5FastLia.plia.

Module PNSENBSR.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat.
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

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).
Abbreviation ec_state := (NEM.ec_state RSEGS CAD).

(* [comment removed for export] *)
Lemma bytes_of_defined M a : forall (m : nat), L5.defined M a (Z.of_nat m) -> 0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
  exists bs, length bs = m /\ L5.bytes_at RSEGS M a bs /\ bytes_ok bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_300 ())). Qed.

Section Call.
Hypothesis SPM : NESK.sp_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat p d n : Z) (bs : list Z).
Variables (en : enc) (k : NESK.sink) (b e : bool) (ea : NECS.eargs).
Hypothesis EAN : NECS.ea_n ea = n.
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 4.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 p.
Hypothesis Hp1 : sp <= p.
Hypothesis Hp2 : p + 16 <= ov.
Hypothesis VOK : NECS.view_ok RSEGS M sp ov LBX p d n.
Hypothesis BS : L5.bytes_at RSEGS M d bs.
Hypothesis BSL : Z.of_nat (length bs) = n.
Hypothesis BOK : bytes_ok bs.
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
Hypothesis PRE : NESK.sk_z k + n + 6 <= NESK.SMZ.
Hypothesis CRED : PMSP.credit_le (NECS.pot_enc L P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
                         (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_atP M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS CAD M' -> PQST.err_ok RSEGS CAD AQ M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> NECS.step_view ea en k b en' k' b' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 4) (NECS.W_enc CAD ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (NECS.pot_enc L P en k) (NECS.pot_enc L P en' k') ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Let cells : list (Z * Z) := [(sp - 8, bv_unsigned (getr R (PMK.reg 1))); (sp - 16, bv_unsigned (getr R (PMK.reg 8))); (sp - 24, bv_unsigned (getr R (PMK.reg 9)));
                             (sp - 32, bv_unsigned (getr R (PMK.reg 18))); (sp - 40, bv_unsigned (getr R (PMK.reg 19))); (sp - 48, bv_unsigned (getr R (PMK.reg 20)))].
Let CINV := (NECK.cinv L HI P M model LBX cr sp ov osk en k 20480 cells).
Lemma COK : NECK.cells_ok sp 64 cells.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_301 ())). Qed.
Lemma CREDs : PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_302 ())). Qed.
Lemma CXok : NECK.kctx L HI P R M model K LBX cr sp r ov osk en k 4 20480 64.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_303 ())). Qed.
Let Kfacts := NECK.facts_ok L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok.
Let Kfin := NECK.fin_facts AQ L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok oec cat b e.
Let Kcred := NECK.fin_credit L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok.
Let Kstart := NECK.cinv_start L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok.
Let Kframe := NECK.cinv_frame L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok.
Let Kencw := NECK.cinv_encwrite L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok.
Let Kpb := NECK.call_pb L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok cells COK PB.
Let Kntb16 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok cells COK 2 (ne_ntb_u16 EE) NTB16.
Let Kntb32 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 64 CXok cells COK 4 (ne_ntb_u32 EE) NTB32.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

Lemma CSLsub KS Ra Rb : (forall x, In x KS -> getr Rb (PMK.reg x) = getr Ra (PMK.reg x)) -> forallb (fun k0 => existsb (Nat.eqb k0) KS) CSL = true -> csl Ra -> csl Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_304 ())). Qed.
Lemma CSLcall Ra Rb : regs_preserved Ra Rb -> csl Ra -> csl Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_305 ())). Qed.

(* [comment removed for export] *)
Lemma st_facts Mq mdq crq kq lo hi : CINV Mq mdq crq kq lo hi ->
  L5.writable RSEGS Mq (sp - 20480) 20480 /\ L5.writable RSEGS Mq ov 56 /\ L5.u64_at RSEGS Mq (ov + 8) osk
  /\ PMSP.model_ok mdq /\ hi_heap HI (NECS.eown en kq ++ LBX) crq Mq (m_vmmaps mdq) /\ L5C.stk (hl_sptop L) Mq sp 20480
  /\ L5.u64_at RSEGS Mq (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\ L5.u64_at RSEGS Mq (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS Mq (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS Mq (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS Mq (sp - 40) (bv_unsigned (getr R (PMK.reg 19))) /\ L5.u64_at RSEGS Mq (sp - 48) (bv_unsigned (getr R (PMK.reg 20)))
  /\ L5.u64_at RSEGS Mq p d /\ L5.u64_at RSEGS Mq (p + 8) n /\ L5.bytes_at RSEGS Mq d bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_306 ())). Qed.

Local Ltac bvr Rq := pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 9))) as RB9q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 10))) as RB10q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 11))) as RB11q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 12))) as RB12q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 18))) as RB18q;
  change (bv_modulus 64) with (2 ^ 64) in RB9q, RB10q, RB11q, RB12q, RB18q.
Local Ltac bvr0 := pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as RB1; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as RB8;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as RB9; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as RB18;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as RB19; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as RB20;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 12))) as RB12; change (bv_modulus 64) with (2 ^ 64) in RB1, RB8, RB9, RB18, RB19, RB20, RB12.

(* [comment removed for export] *)
Lemma FIN (fx7 : FPState) R7 M7 mdq crq kq lo hi :
  CINV M7 mdq crq kq lo hi -> 0 <= lo -> hi <= n + 6 -> regs_preserved R R7 ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 r M7 mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_307 ())). Qed.

(* [comment removed for export] *)
Lemma ev_tail (fxq : FPState) Rq Mq mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> 0 <= lo -> hi <= n + 6 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 19) = Z_to_bv 64 n -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40eec Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_308 ())). Qed.

(* [comment removed for export] *)
Lemma tail_E (fxq : FPState) Rq Mq mdq crq kq w c :
  CINV Mq mdq crq kq w w -> 0 <= w <= n + 6 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 c -> 1 <= c < 2 ^ 47 ->
  getr Rq (PMK.reg 18) = Z_to_bv 64 1 -> getr Rq (PMK.reg 19) = Z_to_bv 64 n -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40ee0 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_309 ())). Qed.

(* [comment removed for export] *)
Lemma loop (j : nat) : forall (fxq : FPState) Rq Mq mdq crq kq w,
  (1 <= j)%nat -> Z.of_nat j <= n ->
  CINV Mq mdq crq kq w w -> w + Z.of_nat j <= n + 6 -> 0 <= w ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 (d + (n - Z.of_nat j)) ->
  getr Rq (PMK.reg 18) = Z_to_bv 64 (Z.of_nat j) -> getr Rq (PMK.reg 19) = Z_to_bv 64 n -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40ecc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_310 ())). Qed.

(* [comment removed for export] *)
Lemma at_L (fxq : FPState) Rq Mq mdq crq kq (w : Z) :
  CINV Mq mdq crq kq w w -> 0 <= w <= 6 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 p -> getr Rq (PMK.reg 19) = Z_to_bv 64 n -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40ec0 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_311 ())). Qed.

(* [comment removed for export] *)
Lemma at_T (fxq : FPState) Rq Mq mdq crq kq (pc w : Z) :
  (pc = 0x40eb0 \/ pc = 0x40fac \/ pc = 0x40f64) ->
  CINV Mq mdq crq kq w w -> 0 <= w <= 5 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 64) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 p -> getr Rq (PMK.reg 19) = Z_to_bv 64 n -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq pc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_312 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x40e10 M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_313 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem v_bstr_raw_ok : NECS.v_bstr_raw_spec RSEGS CAD AQ EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBsr ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_314 ())). Qed.
End WithHeap.
End PNSENBSR.

End PnSEncBsr.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155.
Module PnSEncBstP.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0007.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BigLinkBase. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BigLinkBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.BigLinkGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0157 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg.Mh_0155.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncBstP () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K6zagreeC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01444L5Kn3L5K5zpolyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z6moduloC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K;zpoly_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@word_of_unsignedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib;BigLinkBase2BL2MMC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u64_of_KWord8C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=u32_of_KWord4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<u8_of_KWord1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K8adenot_eC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z9mod_smallK45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K47Corelib4Init5Logic3and01C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K?defined_of_KUnkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9land_le_rC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z7lor_0_lC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z<log2_lt_pow2C56Stdlib6ZArith6BinInt1Z:max_lub_ltC56Stdlib6ZArith6BinInt1Z8log2_lorC56Stdlib6ZArith6BinInt1Z>log2_lt_cancelC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z9land_commC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib4Init9Datatypes9andb_propC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega5Tauto4kind02C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7kept_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btH8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2tlC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6to_natC59OSSVerify5KrLib7Mh_00079BigLinkZA6za_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00079BigLinkZA8za_startC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG5slotsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG@regs_ok_of_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:zagree_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zpoly_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KRangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KAlignC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K:kentry_KWrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib;BigLinkBase2BL9bvu_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K<kentry_KDisjC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord8C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7SegPlan3SGP8bfact_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH8<seg_sound_axC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01444L5Kn3L5K9zagree_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=outside_nil_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K>outside_cons_eC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG<unsigned_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG9kept_regsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP=word_of_zpolyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG;edenot_keptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP>u64_of_KWord8aC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib7Mh_00079BigLinkZA7za_stepC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP:regions_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP7outsideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0144;BigLinkGlue2BG7out_regC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InI69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH86cells0C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH83kn0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7SegPlan3SGP5bfact00C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtH83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:KS_btH8_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btH8bC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH8b3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btH8b_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ89regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btJ8C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ8<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtJ83ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:KS_btJ8_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btL8zC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtL8z3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btL8z_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btH16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH166cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btH16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW169regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btW16C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW16<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW163ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btW16_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btH32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH326cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtH323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btH32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btW32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtW323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btW32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ329regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btJ32C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ32<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtJ323ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btJ32_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btL1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtL13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:KS_btL1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6KS_btBC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K=kentry_KWord1C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtB3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9KS_btB_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6KS_btNC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtN3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9KS_btN_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6KS_btEC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP4PbtE3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9KS_btE_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV09regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btV0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV0<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV03ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:KS_btV0_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV19regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btV1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV1<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV13NX0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5mulop01c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV13ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:KS_btV1_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP5PbtV16cells0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w9regs_out0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btV1wC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w<seg_sound_axC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w3ps0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP;KS_btV1w_okC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6PbtV1w6cells0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

Module PNSENBTP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_315 ())). Qed.
(* [comment removed for export] *)
Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_316 ())). Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_317 ())). Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_318 ())). Qed.
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_319 ())). Qed.
Lemma defined_of_KUnka E M b off ne a n a' : kentry_ok RSEGS E M (KUnk (SA b off) ne) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E ne) = n -> a' = a + off -> L5.defined M a' n.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_320 ())). Qed.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_321 ())). Qed.
Lemma lor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_322 ())). Qed.
(* [comment removed for export] *)
Lemma land_le_l a m : 0 <= a -> 0 <= m -> Z.land a m <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_323 ())). Qed.
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)); pose proof (land_le_l a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Lemma setbit1_byte a : 0 <= a < 256 -> 0 <= (Z.land a 18446744073709551613 + 2) mod 2 ^ 64 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_324 ())). Qed.
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
Module PbtH8 := BndP_Ns_043.LibSegNs_btH8.
Definition KS_btH8 : list nat := Eval vm_compute in (BG.kept_list 60 PbtH8.regs0 PbtH8.regs_out0).
Lemma KS_btH8_ok : BG.kept_ok 60 PbtH8.regs0 PbtH8.regs_out0 KS_btH8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_325 ())). Qed.
Lemma btH8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 0 <= (V 34%nat) <= 255 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40cfc M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_btH8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265588
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 45)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_326 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtH8b := BndP_Ns_043.LibSegNs_btH8b.
Definition KS_btH8b : list nat := Eval vm_compute in (BG.kept_list 60 PbtH8b.regs0 PbtH8b.regs_out0).
Lemma KS_btH8b_ok : BG.kept_ok 60 PbtH8b.regs0 PbtH8b.regs_out0 KS_btH8b = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_327 ())). Qed.
Lemma btH8b_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 0 <= (V 34%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 44) <= bv_unsigned a < ((V 2%nat) - 44) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 44) <= i < ((V 2%nat) - 44) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40d74 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_btH8b -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265604
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 44)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_328 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtJ8 := BndP_Ns_043.LibSegNs_btJ8.
Definition KS_btJ8 : list nat := Eval vm_compute in (BG.kept_list 60 PbtJ8.regs0 PbtJ8.regs_out0).
Lemma KS_btJ8_ok : BG.kept_ok 60 PbtJ8.regs0 PbtJ8.regs_out0 KS_btJ8 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_329 ())). Qed.
Lemma btJ8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 48) + 48 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40d84 M) (st fx' R' 0x40db8 M')
        /\ (forall x, In x KS_btJ8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_330 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtL8z := BndP_Ns_043.LibSegNs_btL8z.
Definition KS_btL8z : list nat := Eval vm_compute in (BG.kept_list 60 PbtL8z.regs0 PbtL8z.regs_out0).
Lemma KS_btL8z_ok : BG.kept_ok 60 PbtL8z.regs0 PbtL8z.regs_out0 KS_btL8z = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_331 ())). Qed.
Lemma btL8z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M ((V 11%nat) + 8) 0 ->
  (((V 2%nat) - 48) + 48 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40d84 M) (st fx' R' 0x40dd8 M')
        /\ (forall x, In x KS_btL8z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 18) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_332 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtH16 := BndP_Ns_043.LibSegNs_btH16.
Definition KS_btH16 : list nat := Eval vm_compute in (BG.kept_list 60 PbtH16.regs0 PbtH16.regs_out0).
Lemma KS_btH16_ok : BG.kept_ok 60 PbtH16.regs0 PbtH16.regs_out0 KS_btH16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_333 ())). Qed.
Lemma btH16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 256 <= (V 34%nat) <= 65535 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40cfc M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_btH16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265632
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 43)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_334 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtW16 := BndP_Ns_044.LibSegNs_btW16.
Definition KS_btW16 : list nat := Eval vm_compute in (BG.kept_list 60 PbtW16.regs0 PbtW16.regs_out0).
Lemma KS_btW16_ok : BG.kept_ok 60 PbtW16.regs0 PbtW16.regs_out0 KS_btW16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_335 ())). Qed.
Lemma btW16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40da0 M) (st fx' R' 0x41aec M')
        /\ (forall x, In x KS_btW16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265644
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_336 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtH32 := BndP_Ns_043.LibSegNs_btH32.
Definition KS_btH32 : list nat := Eval vm_compute in (BG.kept_list 60 PbtH32.regs0 PbtH32.regs_out0).
Lemma KS_btH32_ok : BG.kept_ok 60 PbtH32.regs0 PbtH32.regs_out0 KS_btH32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_337 ())). Qed.
Lemma btH32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355272 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 56 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 140735332483072 <= (bv_unsigned (getr R (reg 11))) <= 140737488355312 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 11))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 11))) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 65536 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 48) + 48 <= (bv_unsigned (getr R (reg 11))) \/ (bv_unsigned (getr R (reg 11))) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40cfc M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_btH32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265552
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = getr R (reg 11)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 42)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((bv_unsigned (getr R (reg 10))) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_338 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtW32 := BndP_Ns_044.LibSegNs_btW32.
Definition KS_btW32 : list nat := Eval vm_compute in (BG.kept_list 60 PbtW32.regs0 PbtW32.regs_out0).
Lemma KS_btW32_ok : BG.kept_ok 60 PbtW32.regs0 PbtW32.regs_out0 KS_btW32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_339 ())). Qed.
Lemma btW32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 10%nat) + 8) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 0 <= (V 34%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40d50 M) (st fx' R' 0x41b50 M')
        /\ (forall x, In x KS_btW32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265564
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 10%nat) + 8)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_340 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtJ32 := BndP_Ns_043.LibSegNs_btJ32.
Definition KS_btJ32 : list nat := Eval vm_compute in (BG.kept_list 60 PbtJ32.regs0 PbtJ32.regs_out0).
Lemma KS_btJ32_ok : BG.kept_ok 60 PbtJ32.regs0 PbtJ32.regs_out0 KS_btJ32 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_341 ())). Qed.
Lemma btJ32_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 48) + 48 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40d5c M) (st fx' R' 0x40db8 M')
        /\ (forall x, In x KS_btJ32 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_342 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtL1 := BndP_Ns_043.LibSegNs_btL1.
Definition KS_btL1 : list nat := Eval vm_compute in (BG.kept_list 60 PbtL1.regs0 PbtL1.regs_out0).
Lemma KS_btL1_ok : BG.kept_ok 60 PbtL1.regs0 PbtL1.regs_out0 KS_btL1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_343 ())). Qed.
Lemma btL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 11%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 11%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (V 11%nat) <= 140737488355312 -> L5.u64_at RSEGS M (V 11%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 11%nat) + 8) (V 34%nat) -> 0 <= (V 33%nat) <= 140737488355328 -> 1 <= (V 34%nat) <= 536870911 -> (((V 2%nat) - 48) + 48 <= (V 11%nat) \/ (V 11%nat) + 16 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40dac M) (st fx' R' 0x40db8 M')
        /\ (forall x, In x KS_btL1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_344 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtB := BndP_Ns_043.LibSegNs_btB.
Definition KS_btB : list nat := Eval vm_compute in (BG.kept_list 60 PbtB.regs0 PbtB.regs_out0).
Lemma KS_btB_ok : BG.kept_ok 60 PbtB.regs0 PbtB.regs_out0 KS_btB = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_345 ())). Qed.
Lemma btB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) ->
  140735332483072 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 -> 1 <= (V 36%nat) <= 140737488355327 -> L5.u8_at RSEGS M (V 36%nat) (V 37%nat) ->
  0 <= (V 37%nat) <= 255 -> 1 <= (V 38%nat) <= 536870911 -> (((V 2%nat) - 48) + 48 <= (V 36%nat) \/ (V 36%nat) + 1 <= ((V 2%nat) - 48)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 41) <= bv_unsigned a < ((V 2%nat) - 41) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 41) <= i < ((V 2%nat) - 41) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40db8 M) (st fx' R' 0x41d04 M')
        /\ (forall x, In x KS_btB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 265676
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 41)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_346 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtN := BndP_Ns_044.LibSegNs_btN.
Definition KS_btN : list nat := Eval vm_compute in (BG.kept_list 60 PbtN.regs0 PbtN.regs_out0).
Lemma KS_btN_ok : BG.kept_ok 60 PbtN.regs0 PbtN.regs_out0 KS_btN = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_347 ())). Qed.
Lemma btN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 38%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1 <= (V 36%nat) <= 140737488355327 -> 2 <= (V 38%nat) <= 536870911 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40dcc M) (st fx' R' 0x40db8 M')
        /\ (forall x, In x KS_btN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 38%nat) - 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_348 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtE := BndP_Ns_043.LibSegNs_btE.
Definition KS_btE : list nat := Eval vm_compute in (BG.kept_list 60 PbtE.regs0 PbtE.regs_out0).
Lemma KS_btE_ok : BG.kept_ok 60 PbtE.regs0 PbtE.regs_out0 KS_btE = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_349 ())). Qed.
Lemma btE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 1 ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 1 <= (V 36%nat) <= 140737488355327 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40dcc M) (st fx' R' 0x40dd8 M')
        /\ (forall x, In x KS_btE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 36%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_350 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtV0 := BndP_Ns_044.LibSegNs_btV0.
Definition KS_btV0 : list nat := Eval vm_compute in (BG.kept_list 60 PbtV0.regs0 PbtV0.regs_out0).
Lemma KS_btV0_ok : BG.kept_ok 60 PbtV0.regs0 PbtV0.regs_out0 KS_btV0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_351 ())). Qed.
Lemma btV0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 57%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) -> 0 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40dd8 M) (st fx' R' 0x40e0c M')
        /\ (forall x, In x KS_btV0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_352 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtV1 := BndP_Ns_044.LibSegNs_btV1.
Definition KS_btV1 : list nat := Eval vm_compute in (BG.kept_list 60 PbtV1.regs0 PbtV1.regs_out0).
Lemma KS_btV1_ok : BG.kept_ok 60 PbtV1.regs0 PbtV1.regs_out0 KS_btV1 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_353 ())). Qed.
Lemma btV1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 57%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551614 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40dd8 M) (st fx' R' 0x40e0c M')
        /\ (forall x, In x KS_btV1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) ((V 42%nat) + 1)).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_354 ())). Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbtV1w := BndP_Ns_044.LibSegNs_btV1w.
Definition KS_btV1w : list nat := Eval vm_compute in (BG.kept_list 60 PbtV1w.regs0 PbtV1w.regs_out0).
Lemma KS_btV1w_ok : BG.kept_ok 60 PbtV1w.regs0 PbtV1w.regs_out0 KS_btV1w = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_355 ())). Qed.
Lemma btV1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 57%nat) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 18) = Z_to_bv 64 (V 58%nat) ->
  140735332483120 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 48 -> 140735332483072 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 48) + 48 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 48)) -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 48) \/ ((V 2%nat) - 48) + 48 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 39%nat) - 8) <= bv_unsigned a < ((V 39%nat) - 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 39%nat) - 8) <= i < ((V 39%nat) - 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x40dd8 M) (st fx' R' 0x40e0c M')
        /\ (forall x, In x KS_btV1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 39%nat) - 8) 0).
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBstP ()) [] (Mh_0192_blobs1.kr_b_356 ())). Qed.
(* [comment removed for export] *)

End PNSENBTP.

End PnSEncBstP.
Module PnSEncBst.
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
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_3fce0_41034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0142.PnKitS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PnQKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0146.PnEncCall OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmCertKitG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0192.PnSEncBstP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_3fce0_41034.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_PnSEncBst () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List8map_consC69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K@nth_error_singleC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_01028NemModel3NEM8bytes_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic9False_indK47Corelib5Lists7ListDef6Forall01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega=RingMicromega7Formula01C56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesI47Corelib4Init5Peano2le00I47Corelib4Init5Logic2or00C47Corelib4Init3Nat3subC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic6eq_symC35stdpp7tactics<f_equal_helpC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2C47Corelib4Init9Datatypes3appI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes7nat_indC47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib7Mh_00846L5Defs2L58bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_geK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00K46Stdlib9micromega=RingMicromega3Op201I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op204I46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK8cells_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib7Mh_01028NemModel3NEM6enc_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout5ne_vtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_nC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib7Mh_01028NemModel3NEM4en_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM4ecapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8en_depthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface;block_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP2T4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK9cred_sinkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0018:NemLayoutS8NEADDR_SC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM9MAX_DEPTHC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM3ESZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5ESIZEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM5EKMAXC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01048PnSpecsS3PMS6layout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00849HeapIface=heap_iface_ok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01027NemSink4NESK>sink_policy_ok00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK5sp_hbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP6pm_scrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4eownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC59OSSVerify5KrLib7Mh_00849HeapIface7hi_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP8model_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP5entryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface8hl_sptopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sink_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4kctxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK3SMZC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C59OSSVerify5KrLib7Mh_00189PnLayoutS6ADDR_SC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST5CREDsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC56Stdlib5Arith8PeanoNat3Nat3eqbC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbc69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3cslC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01498PnEncKit4NEKT6sub_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3CSLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK?cs_of_preservedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01359L5CoreKit3L5K9In_of_memC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indC69OSSVerify5KrLib7Mh_01356PmStep3PMK6cs_allC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List:in_app_iffC59OSSVerify5KrLib7Mh_00849HeapIface<model_but_vmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK4sk_zC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2ekC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK2dkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L55ra_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_gpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00188PmLayout5pa_tpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9hl_img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7view_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00905PgSrc3PGS6in_blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC46Stdlib5Lists4List9incl_reflC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR>brange_of_heapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM7enc_ownC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK8sink_ownC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyK47Corelib4Init5Logic2or02C47Corelib4Init5Logic7and_indC46Stdlib5Lists4List4inclC69OSSVerify5KrLib7Mh_01357PmFrame4PMFR;brange_inclC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR6brangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK3inWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8inW_inv1C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_00906L5Core3L5C<stk_writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5CCwritable_of_definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8u64_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR8ag_blockC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C<agree_on_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR9brange_hiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC69OSSVerify5KrLib7Mh_00906L5Core3L5C>bytes_at_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01357PmFrame4PMFR5ag_hiC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP;credit_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_01027NemSink4NESK4sink00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveK46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5W_encC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00906L5Core3L5C5hpresC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS4ea_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS9step_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP3cfgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemModel3NEM8ec_stateC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00909PmStatics4PMST7base_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0090:PnQStatics4PQST6err_okC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemModel3NEM3enc00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST8st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC69OSSVerify5KrLib7Mh_01358PmParKit4PMPK7word_idC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7alignedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8btE_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST6CSLsubC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST7ev_tailC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9spiece_roC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6KS_btEC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6nth_InC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List=Forall_forallC69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphc69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8btB_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK9cwr_stackC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK7rng_decC1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib7Mh_01469PnEncCall4NECK4cinvC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith6Zorder9Zle_0_natC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST7CSLcallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST6tail_EC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8btN_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01356PmStep3PMK6spieceC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6KS_btBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP6KS_btNC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST3COKC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btL8z_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9btL1_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP9btJ8_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP:btJ32_concC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST4loopC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btL8zC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btL1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP7KS_btJ8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0192:PnSEncBstP8PNSENBTP8KS_btJ32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01027NemSink4NESK7sp_modeC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS:eargs_bstrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS8pre_viewC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS7pot_encC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST@bytes_of_definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01929PnSEncBst8PNSENBST4mainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00189NemLayout;ne_bstr_tagC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS?v_bstr_tag_specC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5eargs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01028NemSpecs4NECS5ENC_HC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01". Local Ltac lia := L5FastLia.plia.

Module PNSENBST.
Import PMS.
Import NEM.
Abbreviation CAD := PMS.AD.
Abbreviation EE := NemLayoutS.NEADDR_S.

(* [comment removed for export] *)
Definition CSL : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
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

Abbreviation enc_at := (NEM.enc_at RSEGS EE L PMSP.T3 PMSP.T4).
Abbreviation sink_atP := (NESK.sink_at RSEGS L PMSP.T3 PMSP.T4 P).
Abbreviation ec_state := (NEM.ec_state RSEGS CAD).

(* [comment removed for export] *)
Lemma bytes_of_defined M a : forall (m : nat), L5.defined M a (Z.of_nat m) -> 0 <= a -> a + Z.of_nat m <= 2 ^ 64 ->
  exists bs, length bs = m /\ L5.bytes_at RSEGS M a bs /\ bytes_ok bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_357 ())). Qed.

Section Call.
Hypothesis SPM : NESK.sp_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (cr : credit) (sp r ov osk oec cat p d n : Z) (bs : list Z).
Variables (en : enc) (k : NESK.sink) (b e : bool) (ea : NECS.eargs).
Hypothesis EAN : NECS.ea_n ea = n.
Hypothesis HH : hi_heap HI (NECS.eown en k ++ LBX) cr M (m_vmmaps model).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSP.entry CAD L R M sp r 4.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 ov.
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 p.
Hypothesis Hp1 : sp <= p.
Hypothesis Hp2 : p + 16 <= ov.
Hypothesis VOK : NECS.view_ok RSEGS M sp ov LBX p d n.
Hypothesis BS : L5.bytes_at RSEGS M d bs.
Hypothesis BSL : Z.of_nat (length bs) = n.
Hypothesis BOK : bytes_ok bs.
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
Hypothesis PRE : NESK.sk_z k + n + 6 <= NESK.SMZ.
Hypothesis CRED : PMSP.credit_le (NECS.pot_enc L P en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model)
                         (en' : enc) (k' : NESK.sink) (b' e' : bool) (cr' : credit),
        regs_preserved R R' ->
        enc_at M' ov osk en' -> sink_atP M' osk k' -> ec_state M' oec b' cat -> PMST.base_ok RSEGS CAD M' -> PQST.err_ok RSEGS CAD AQ M' e' ->
        (b = true -> b' = true) -> (e = true -> e' = true) -> NECS.step_view ea en k b en' k' b' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 4) (NECS.W_enc CAD ov osk oec) M M' ->
        PMSP.credit_keep cr cr' (NECS.pot_enc L P en k) (NECS.pot_enc L P en' k') ->
        model_but_vm model model' -> hi_heap HI (NECS.eown en' k' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (PMSP.cfg RSEGS R' r M' model') K.

(* [comment removed for export] *)
Let cells : list (Z * Z) := [(sp - 8, bv_unsigned (getr R (PMK.reg 1))); (sp - 16, bv_unsigned (getr R (PMK.reg 8))); (sp - 24, bv_unsigned (getr R (PMK.reg 9)));
                             (sp - 32, bv_unsigned (getr R (PMK.reg 18))); (sp - 40, bv_unsigned (getr R (PMK.reg 19)))].
Let CINV := (NECK.cinv L HI P M model LBX cr sp ov osk en k 20480 cells).
Lemma COK : NECK.cells_ok sp 48 cells.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_358 ())). Qed.
Lemma CREDs : PMSP.credit_le (NESK.sink_pot P (NESK.sk_c k)) cr.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_359 ())). Qed.
Lemma CXok : NECK.kctx L HI P R M model K LBX cr sp r ov osk en k 4 20480 48.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_360 ())). Qed.
Let Kfacts := NECK.facts_ok L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kfin := NECK.fin_facts AQ L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok oec cat b e.
Let Kcred := NECK.fin_credit L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kstart := NECK.cinv_start L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kframe := NECK.cinv_frame L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kencw := NECK.cinv_encwrite L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok.
Let Kpb := NECK.call_pb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK PB.
Let Kntb16 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 2 (ne_ntb_u16 EE) NTB16.
Let Kntb32 := NECK.call_ntb L HI P R M model K LBX cr sp r ov osk en k 4 20480 48 CXok cells COK 4 (ne_ntb_u32 EE) NTB32.
Definition csl (Ri : bvmap 5 word) : Prop := forall j, In j CSL -> getr Ri (PMK.reg j) = getr R (PMK.reg j).

Lemma CSLsub KS Ra Rb : (forall x, In x KS -> getr Rb (PMK.reg x) = getr Ra (PMK.reg x)) -> forallb (fun k0 => existsb (Nat.eqb k0) KS) CSL = true -> csl Ra -> csl Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_361 ())). Qed.
Lemma CSLcall Ra Rb : regs_preserved Ra Rb -> csl Ra -> csl Rb.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_362 ())). Qed.

(* [comment removed for export] *)
Lemma st_facts Mq mdq crq kq lo hi : CINV Mq mdq crq kq lo hi ->
  L5.writable RSEGS Mq (sp - 20480) 20480 /\ L5.writable RSEGS Mq ov 56 /\ L5.u64_at RSEGS Mq (ov + 8) osk
  /\ PMSP.model_ok mdq /\ hi_heap HI (NECS.eown en kq ++ LBX) crq Mq (m_vmmaps mdq) /\ L5C.stk (hl_sptop L) Mq sp 20480
  /\ L5.u64_at RSEGS Mq (sp - 8) (bv_unsigned (getr R (PMK.reg 1))) /\ L5.u64_at RSEGS Mq (sp - 16) (bv_unsigned (getr R (PMK.reg 8)))
  /\ L5.u64_at RSEGS Mq (sp - 24) (bv_unsigned (getr R (PMK.reg 9))) /\ L5.u64_at RSEGS Mq (sp - 32) (bv_unsigned (getr R (PMK.reg 18)))
  /\ L5.u64_at RSEGS Mq (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
  /\ L5.u64_at RSEGS Mq p d /\ L5.u64_at RSEGS Mq (p + 8) n /\ L5.bytes_at RSEGS Mq d bs.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_363 ())). Qed.

Local Ltac bvr Rq := pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 9))) as RB9q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 10))) as RB10q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 11))) as RB11q;
  pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 12))) as RB12q; pose proof (bv_unsigned_in_range 64 (getr Rq (PMK.reg 18))) as RB18q;
  change (bv_modulus 64) with (2 ^ 64) in RB9q, RB10q, RB11q, RB12q, RB18q.
Local Ltac bvr0 := pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as RB1; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as RB8;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as RB9; pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as RB18;
  pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as RB19; change (bv_modulus 64) with (2 ^ 64) in RB1, RB8, RB9, RB18, RB19.

(* [comment removed for export] *)
Lemma FIN (fx7 : FPState) R7 M7 mdq crq kq lo hi :
  CINV M7 mdq crq kq lo hi -> 0 <= lo -> hi <= n + 6 -> regs_preserved R R7 ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS R7 r M7 mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_364 ())). Qed.

(* [comment removed for export] *)
Lemma ev_tail (fxq : FPState) Rq Mq mdq crq kq lo hi :
  CINV Mq mdq crq kq lo hi -> 0 <= lo -> hi <= n + 6 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40dd8 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_365 ())). Qed.

(* [comment removed for export] *)
Lemma tail_E (fxq : FPState) Rq Mq mdq crq kq w c :
  CINV Mq mdq crq kq w w -> 0 <= w <= n + 6 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 c -> 1 <= c < 2 ^ 47 ->
  getr Rq (PMK.reg 18) = Z_to_bv 64 1 -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40dcc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_366 ())). Qed.

(* [comment removed for export] *)
Lemma loop (j : nat) : forall (fxq : FPState) Rq Mq mdq crq kq w,
  (1 <= j)%nat -> Z.of_nat j <= n ->
  CINV Mq mdq crq kq w w -> w + Z.of_nat j <= n + 6 -> 0 <= w ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 (d + (n - Z.of_nat j)) ->
  getr Rq (PMK.reg 18) = Z_to_bv 64 (Z.of_nat j) -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq 0x40db8 Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_367 ())). Qed.

(* [comment removed for export] *)
Lemma at_L (fxq : FPState) Rq Mq mdq crq kq (pc w : Z) :
  (pc = 0x40dac \/ pc = 0x40d84 \/ pc = 0x40d5c) -> (pc = 0x40d84 \/ 1 <= n) ->
  CINV Mq mdq crq kq w w -> 0 <= w <= 5 ->
  getr Rq (PMK.reg 2) = Z_to_bv 64 (sp - 48) -> getr Rq (PMK.reg 8) = Z_to_bv 64 ov -> getr Rq (PMK.reg 9) = Z_to_bv 64 p -> getr Rq (PMK.reg 18) = Z_to_bv 64 n -> csl Rq ->
  srealizes RSEGS SCFG (PMSP.cfg RSEGS Rq pc Mq mdq) K.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_368 ())). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma main : srealizes RSEGS SCFG (PMSP.cfg RSEGS R 0x40cfc M model) K.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0192 ()) ["WithHeap"; "Call"] (Mh_0192_blobs1.kr_b_369 ())). Qed.
End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem v_bstr_tag_ok : NECS.v_bstr_tag_spec RSEGS CAD AQ EE L HI P.
Proof.
ltac2:(KReplay.run1 (kr_t_PnSEncBst ()) ["WithHeap"] (Mh_0192_blobs1.kr_b_370 ())). Qed.
End WithHeap.
End PNSENBST.

End PnSEncBst.
