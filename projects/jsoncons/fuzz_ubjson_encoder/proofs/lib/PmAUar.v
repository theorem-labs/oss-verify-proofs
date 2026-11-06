(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import HeapIfaceAEx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepAR L5CoreBR L5ADetailHR PmLayout PeLayoutA PmModel PmSpecsA PeSpecsAa PgSrcA PmAUarK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PmAUar () := "C47Corelib7Program6Basics4flipC46Stdlib5Lists4List2InC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6fframeC13~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55rangeC13~~~I35stdpp4base5NoDup00C35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I47Corelib4Init9Datatypes4list00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA7ffroomAC13~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ff_countC13~~~C56Stdlib6ZArith6BinInt1Z6of_natC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ff_capC13~~~C47Corelib4Init3Nat3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR<ff_count_appC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR=ff_count_consC13~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SARBnodup_of_map_app_rC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR=ff_count_inclC13~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8eq_ind_rC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7ff_addrC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA5ffrsAC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA5ff_rsC13~~~K46Stdlib9micromega6VarMap1t01I47Corelib4Init5Logic2or00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA9frame_okAC13~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01I47Corelib4Init5Logic3and00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmSpecsA5PMSPA5aobjAC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ff_classC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ff_bytesC13~~~C56Stdlib6ZArith6BinInt1Z3subC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6PgSrcA4PGSA7ffroomBC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7ff_roomC13~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6or_indI47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6vml_ofC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA6ri_invC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan7L5CoreA4L5CA9amodel_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan7L5CoreA4L5CA4astkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk9mem_growsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR2ekC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR2dkC13~~~K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA5hl_tpC13~~~C56Stdlib6ZArith6BinInt1Z3powI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmAUarK5PMAUK4gctx00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface>regs_preservedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8model_rtC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5L5KnA4L5KA8zeros_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57definedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A4avisC13~~~C56Stdlib6ZArith6BinInt1Z3divC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7aclientC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A3cfgC13~~~C56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic7and_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8ar_sptopC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<ar_stack_topC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeSpecsAa3PMA5SM_PCC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJAaior_stack_mallocC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceABastack_malloc_specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7hl_segsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare6ret_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceAChl_scr_stack_mallocC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9astack_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA5ar_fsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9hl_img_loC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9hl_img_hiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA=fframes_apartC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7definedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7cell_isC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA;shadow_zeroC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA:aheap_presC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA?hl_stack_mallocC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A8aly_segsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeSpecsAa3PMA5ly_smC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:aly_scr_smC13~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5<unsigned_litC13~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5Hoare;ret_ok_evenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SARAastack_ok_of_astkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA7app_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR8sm_factsC13~~~C56Stdlib6ZArith6BinInt1Z3mulC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ?model_rt_haltedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR=astk_after_rtC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<hl_rt_staticC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR<aclient_appbC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR=aclient_casesC13~~~C47Corelib4Init5Logic3notC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA1SC13~~~C46Stdlib5Lists4List9in_or_appC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SARBfframes_apart_inclC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SARFfresh_frame_not_clientC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR<stack_clientC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmAUarK5PMAUK4gctx01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan7L5CoreA4L5CA5akeptC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L57outsideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR<aclient_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR8ek_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR8dk_transC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR8sm_apartC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L58writableC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56u64_atC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr05C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA2SBC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8FS_BYTESC13~~~I47Corelib4Init5Logic4True00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<in_shadow_ofC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmAUarK5PMAUK5WretXC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ7aior_wfC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA<ablock_rangeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9ff_removeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA?ar_stack_bottomC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmAUarK5PMAUK4WretC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8in_blockC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9in_fframeC13~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ;shadow_blkRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA>shadow_allowedC13~~~C56Stdlib6ZArith6BinInt1Z7div_posC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:aly_img_loC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5DefsA3L5A:aly_img_hiC13~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z7div_addC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z7div_mulC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR:aclient_00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR<aclient_consC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4asan8L5StepAR5L5SAR8ek_pieceC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface9lb_removeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface<blocks_apartC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA9aclient_gC13~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib;setoid_ring6Ncring;eq_notationC47Corelib7Classes9Morphisms?eq_proper_proxyC46Stdlib;setoid_ring6Ncring=ring_sub_compC46Stdlib;setoid_ring6Ncring>ring_plus_compC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA3vmlC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6PmAUar6PMAUAR3WfrC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L59frame_butC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L56in_rngC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L5=defined_growsC13~~~". Local Ltac lia := L5FastLia.plia.

Module PMAUAR.
Import L5A. Import L5CA. Import L5SAR.
Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma ffroomA_push h h' FF LK LK2 (f : fframe) :
  PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr ((f :: FF) ++ LK2)) -> h' + 1 <= h -> PMSPA.ffroomA h' (f :: FF) LK2.
Proof. 
intros FR INC ND Hh k Hk. specialize (FR k Hk). rewrite ff_count_app in FR. rewrite ff_count_app.
pose proof (ff_count_cons k f FF) as C1.
pose proof (ff_count_incl k LK2 LK INC (nodup_of_map_app_r (f :: FF) LK2 ND)) as C2. lia.
Qed.
Lemma ffrsA_push FF sp sp' F k rs : PMSPA.ffrsA FF sp -> sp' + 32 <= rs -> sp' <= sp -> PMSPA.ffrsA ((F, k, rs) :: FF) sp'.
Proof.  intros H1 H2 H3 f [<-|Hf]; [cbn; lia| specialize (H1 f Hf); lia]. Qed.
Lemma frame_okA_push FF fb F k rs : PMSPA.frame_okA FF fb -> PMSPA.frame_okA ((F, k, rs) :: FF) fb.
Proof.  intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.
Lemma aobjA_push FF o n f : PMSPA.aobjA FF o n -> PMSPA.aobjA (f :: FF) o n.
Proof.  intros (g & Hg & X). exists g. split; [right; exact Hg| exact X]. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ffroomB_push FC h h' FF LK LK2 (f : fframe) :
  PGSA.ffroomB FC h FF LK -> incl LK2 LK -> NoDup (map ff_addr ((f :: FF) ++ LK2)) -> h' + 1 <= h -> PGSA.ffroomB FC h' (f :: FF) LK2.
Proof.
ltac2:(KReplay.run1 (kr_t_PmAUar ()) [] "h01xh12FRh21nh32C0h42FCh52FFh62LKh73LK2h84__x1h94__x2h:4__x3h;4__x4h<4__x5h=4__x6h>4__x7h?1fh@1hhA2h'hB2C1hC2C2hD3FR0hE2HhhF2HkhG3INChH2NDhI7__arithhJ4__ffhK8__varmaphL5__withM4cstrhN5cstr0hO5cstr1hP5cstr2hQ1khR1mhS1yp;1p;4p;3p;2p;6p;5p;Bp;<p;7p;8g006Kj1ITg00m]j4XTg003cj3bTg003Fj3CTg0021j4qTg005Fj2eTg008<j1UTg008ZR0j23Tg0097R1j21Tg000Nj3\Tg00;]j20Tg00<kR2j12Tg009Sj1GTg00=Kj17Tg00>Wj2@Tg00>nj3TTg002Mj6lTg00@Ij3dTg00AeR3j1:Tg00BDR4j2ATg00B^j3aTg00D?j5_Tg00E[j1^Tg00F9j4]Tg00F\j4FTg00GCj1>Tg00Ghj2<Tg00HQj3BTg00I:j2ZTg00:]j1YTg00;=j3KTg00Ifj2ETg00JDj4JTg00Jbj1sTg00K@j1rTg00:8j1HTg00Kkj2WTg00LNj1pTg00M0j2VTg00MSj2oTg00N5j2QTg00NOj2kTg00O;j3jTg00OUj3iTg00P4j4fTg00Pfj4gTg00QQj6hTg00QolBRTg00RUl<PTg00S:l<STg00S_j3cTg00TBj4mTg00Tmj7nTg00UQj8`Tg000eR5f1R6f0R73Kp=6f2R8/36/37p=9g00V5R9/Q7p=4g00VSR:P:P:P9P9P9g00W2P2P2P2P0g00WRf5R;f4R<f3R=P8P6P7MBRp=OP:P9P9P9P2P2P;P<P=P8P6P7M<Pp=NP9P9P9P9P9P9P0P7P6P8P0P=P<P;f6R0f7R>f8R?f9R@MBRp=?P9P9P1P>P1P0P;P<P=P8P6P7M<Sp=MP:P9P4P2P1g00X5P;P<P=P8P6P7M<Sp=LP:P:P9P9P3P2P2P=g00XWP8P6P7M<Pp=[1V97p=8Ac967p=5P9P6g00Y;P7Cmp=;P6g00YbR2g00ZAR3P3g00ZaR1P7g00[AFnp==P=P2P3P3P1P8P6P7G`p=D%I9R2%I5R4P0P;P=P8CXAb58=P5P9g00[a168;=C5=Cq,e9g00\nRA#URB,3>RC/1?f;RD9\97P;P6P7O2AC5@?,06#2%GARE#URF79D%76'1P:f:RG=C5@,08%27RHf=RI;9FRJ%7='1X2:P7108G108@'@RKAT8G@El%2Kf<RK;9F%78'1P:16?DRL,0=RM10=@'@%7<,1JX2:Ad=?D10=D#:,AMP<PGPDP>16@K?aG0D_10<G10<D'A16GI,0;RM10;DRJ'@RN#2ROf>RP'3RQ/3FRR%7;RS'1%2MRT%2JRU'3RV/3PRW/3FRX/1SP7X09RY1167#^XS9X09RZPRPXPYPYPYP9P9g00^11367C]#4XR9X29RXPQPWPYPYPYPXPOPVPYPY%4HX0:R:PNPVPMPT%4TPJPU%4URTEOENPPPP%4PM:?PFPF%4FRMM:?PSPS%4SGM10;KRK,AJ%2KRS,1URVPJPUPTPKPS%4SELP7CFPV16DP,00RV100PRS#:RK'A%2VRT%2SRU/3B'1RJPVPT%4TPK137BX09RKPUO1PKPSPU%4UC[ELP8CFPJf?,0>RJ10>PRU'@RS#2RKfART'3RV/3FRN%7>RH'1%2JRO%2URW'3RQ?9TF/1HRRPYPZPNPYPQO1RN/3TRZ/3FPYPYPYPXPVPZPYPYPYPXPKPNPYPYP:PSPQPJPO%4OPUPW%4WEOENPTPT%4TM:?PFPFPMM:?PHPH%4HGMP<CFPRf@,0?RR#>g00]SRH%2R'116PT,0@RR#>%2R,1H10GTRR#>%2R,1H10DTRT#>%2T,1Hg00^URTg00_ARD#:RR#:RM#:RW#:,<91<9W1<9M1<9R1<9D5B95B95B95B9g00_`'Z%YT3K%ITP9P91E9<P81E90CJP6P91E9;P=1E9>CJCJ%s9%r9RT%HARD#H#8RR%GD#8RM'5%HE#8RW'51W9FRU'5%GE#8RO';,=T%p3R3PT1V9ARA1W9BRJ,5R';,=TP3PT%8ERE/;M,=TP3PT%8DRD/5J/;W,=TP315AE/5D/5U/;O,=TCDCDCDCD1oT1P7P8g00`LRTg00`lR1'Q1k78=jT1dAi9H6CfbJbKbLX89X99X:9X;9X<9X=9X>9130;?9<F/1=116C11=>13;B/1>13<;?90F/1>[[[[^89^99^:9^;9^<9^=9^>9P7fERF,0I#2fD,0I#2fG%7IfFfC,0I#2fB/6F,0I#2P;P0P>PPO;bIbPbObNbMbDb3b3CgbCbBAC5L@,0=AT=L@Ehb1b1WFXQ9PGP?16<>P;CXeWEWHWGW1X?5X74X64X54XA9X@9X42P0P;P<P=P8P6P7O7X?5X74X64W5XA9X@9W4o"). Qed.
Lemma ff_room_ofB FC h FF LK k : PGSA.ffroomB FC h FF LK -> 0 <= h -> In k FC -> ff_room k FF LK.
Proof.
ltac2:(KReplay.run1 (kr_t_PmAUar ()) [] "h02FCh12FFh22FRh32LKh44__x1h54__x2h64__x3h71hh81kh92Hhh:2Hkh;7__arithh<4__ffh=8__varmaph>5__with?4cstrp;1p;4p;2p;3p;7p;8g006Kj15Tg00m]j4WTg0097j20Tg000Nj3DTg003Fj34Tg00;]j26Tg00<kj17Tg008Zj21Tg009Sj1FTg008<j1ETg00=Kj1>Tg00GCj1BTg00Aej1?Tg00Ghj2:Tg00HQj3@Tg00I:j2VTg00:]j1UTg00;=j3TTg00Ifj2;Tg00JDj4LTg00Jbj1KTg00K@j1ITg00Kkj2<Tg00:8j1GTg00M0j23Tg00LNj1HTg00S_j32Tg00MSj2JTg00N5j2CTg00NOj2MTg00O;j3NTg00OUj3OTg00P4j4PTg00nkj3QTg00TBj4ATg00Tmj7RTg00UQj8STg00V5R0f1R1g00Y;f0R2CAp=9P1g00YbR3g00ZAR4P4g00ZaR5P2g00[AFRp=8f3R6P3P4P4P5f2R3P1P2GSp==%50R7g000eR8#5R9f4R:P6P3P1CWg00]SR;/0:f6R<9D03P3P6P2O2f5R==48:,66#7/1<g00\nR>#FR?#ER@'1%>6'0A48<=,6:RA#B%7A,0;g00^URAg00_ARB#?RC#?,:01:0C1:0B5@05@0g00_`'V%UA3T%5AP01;03P11;06CL%K0%I0RA1<0;%G>,30RB'9,8A%H4R4PA130>R>=20B1<0@RB520130?R?'9,8AP4A20>B/9?,8AC=C=1JA5P2P3g00`LRAg00`lR5'C1M23=NA5dAO0;1CPb<b=b>X40X50X6010;31116/1@/03113@/06[[^40^50^60P2f9%><f8f7548,6<#7P:P3O5b;b?AQ:<=eb2W:W9W2X80X39X19X70X07P:P6P3P1P2O5X80X39W1X70W0o"). Qed.
Lemma classB_in6 k : In k [0; 1; 2; 3; 5] -> In k [0; 1; 2; 3; 4; 5].
Proof.
ltac2:(KReplay.run1 (kr_t_PmAUar ()) [] "h01Hh12H0h21kh32Hkp;1p;3p;2p;6g008<j19Tg009Sj1>Tg00:8j1;Tg00:]j1?Tg00;=j3:Tg000Nj3<Tg00eDj21Tg0108j37Tg00gkj32Tg010Rj2@Tg0111j68Tg00O;j3=Tg00V5R0f1R1f0R23:p=4g00]SR3==02p=5A=012p=0g011MR4,12p=6f2R51112'1p=3g00\nR6#9R7%>6R8#9R9%;6#9R6%;8#9R:%?0'4R;'4'4'49:039<02%51R<1071R=1091R>1061R?10:1#6R@'133RA%>8#9R8/01/1@93>?93<=%55R=1075R?1095R>1065R@108510:5#6R53333RB;72X0<P?A3>@5R511=Bf3RB#5R=107BR@109BR>106BR<108B10:B#6RB'133RC'1RDA7@C232X1?P>11<BRB11=Df4RD#5R=107DR<109DR?106DRC108D10:D#6RD33R@'1RE'1RFA7?@292<E32X0>PCPD11=Ff5RF#5R=107FR>109FRE106FR<108F10:FRF#6'1R@'1R?'1RG'1RHA7<@292E?92>G32X1CPFP411=Hf6RH#5R=107HRC109HRG106HR>108HR?10:HRH#6R:'1RE'1R@'1R<'1RIA7H4292?:92>E92G@92C<32X0F11=I/@2X04P2E8X1DP2E8X0BP2E8X15P2E8X0AP2E8148;,46,49,479:039<01eW3X20P2O1X20o"). Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Lemma uar_sm (k : Z) (LB BX0 : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z))
      (E SCR spc olo ohi : Z) (ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
      (fx : FPState) (R1 : bvmap 5 word) (M M1 : word -> option byte) (model model1 : Model) (K : TSet) (rr : Z) :
  In k [0; 1; 2; 3; 5] ->
  ri_inv HI (BX0 ++ LB) FF LK cr A M (vml_of model) ->
  ri_inv HI (BX0 ++ LB) FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> K [] ->
  astk ar M E SCR -> mem_grows M M1 -> ek L ar LB FF E SCR [] M M1 -> dk L ar LB FF E SCR M M1 ->
  getr R1 2%bv = Z_to_bv 64 spc -> getr R1 4%bv = Z_to_bv 64 (hl_tp L) -> getr R1 1%bv = Z_to_bv 64 rr -> rr mod 2 = 0 -> 0 <= rr < 2 ^ 64 ->
  spc mod 16 = 0 -> E - SCR + 512 <= spc -> spc <= olo -> olo <= ohi -> ohi <= E ->
  (forall a, ocell a -> olo <= a < ohi) ->
  (forall M1 M1', own M1 -> (forall a, ocell a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own M1') ->
  ff_room k FF LK -> (forall f, In f FF -> E + 32 <= ff_rs f) ->
  (forall (R2 : bvmap 5 word) (M2 : word -> option byte) (model2 : Model) (F fl : Z) (LK2 : list fframe),
     PMAUK.gctx L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0 ->
     getr R2 10%bv = Z_to_bv 64 F -> regs_preserved R1 R2 -> amodel_ok A model2 -> model_rt model1 model2 ->
     astk ar M2 E SCR -> ek L ar LB FF E SCR [] M M2 -> dk L ar LB FF E SCR M M2 ->
     ek L ar (BX0 ++ LB) FF E SCR [] M1 M2 -> dk L ar (BX0 ++ LB) FF E SCR M1 M2 ->
     (forall a, spc <= a < E -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
     L5.writable RSEGS (mrestrict (ahid A model2) M2) F (ff_bytes k) ->
     L5.writable RSEGS (mrestrict (ahid A model2) M2) (F / 8 + SB) (ff_bytes k / 8) ->
     L5KA.zeros_at (mrestrict (ahid A model2) M2) (F / 8 + SB) (ff_bytes k / 8) ->
     L5.u64_at RSEGS (mrestrict (ahid A model2) M2) (F + ff_bytes k - 8) fl -> L5.writable RSEGS (mrestrict (ahid A model2) M2) fl 1 ->
     L5.defined (mrestrict (ahid A model2) M2) F (ff_bytes k) ->
     avis (ahid A model2) F (ff_bytes k) -> avis (ahid A model2) (F / 8 + SB) (ff_bytes k / 8) -> avis (ahid A model2) fl 1 ->
     (forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (BX0 ++ LB) FF sp0 scr0 (a + i)) -> 0 < n ->
         (a + n <= F \/ F + ff_bytes k <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes k / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a)) ->
     srealizes RSEGS SCFG (@L5A.cfg fx R2 rr M2 model2) K) ->
  srealizes RSEGS SCFG (@L5A.cfg fx R1 (PMA.SM_PC k) M1 model1) K.
Proof. 
intros Hk HH HH1 AM1 K0 ASTK MG01 EK01 DK01 G2 G4 G1 RR0 RR1 SP16 SPSC SPO1 SPO2 SPO3 OCR OWNAG FFRk FFRS KONT. assert (Hk6 : In k [0; 1; 2; 3; 4; 5]) by (simpl in Hk |- *; tauto).
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
pose proof (HAJ.aior_stack_malloc _ _ _ _ _ HIok k Hk) as SM. unfold astack_malloc_spec in SM.
rewrite (aly_segs L C LYa), (PMA.ly_sm L C LY k Hk), (aly_scr_sm L C LYa) in SM.
assert (U2 : bv_unsigned (getr R1 2%bv) = spc) by (rewrite G2; apply L5.unsigned_lit; clear - SPSC SPO1 SPO2 SPO3 SHI SPT SLO; lia).
eapply (SM fx R1 M1 model1 (BX0 ++ LB) FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
- exact G4.
- rewrite G1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by exact RR1. exact RR0.
- rewrite U2. replace spc with (E - (E - spc)) by (clear; lia).
apply (astack_ok_of_astk L ar C LYa M M1 E SCR (E - spc) 512 ASTK MG01); [clear - SPO1 SPO2 SPO3; lia| clear; lia| clear - SPSC; lia|].
replace (E - (E - spc)) with spc by (clear; lia). exact SP16.
- exact FFRk.
- intros f Hf. rewrite U2. specialize (FFRS f Hf). clear - FFRS SPO1 SPO2 SPO3. lia.
- exact K0.
- intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
rewrite U2 in FLNC, PRES2, HH2. rewrite G1.
pose proof (sm_facts L ar C HI LYa HIok (BX0 ++ LB) FF LK2 cr A M2 model2 F k (spc + 32) fl HH2 Hk6 FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
as (FR & FFL & F32 & F8 & B64 & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
assert (Hh2 : m_halted model2 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT2); exact (proj1 AM1)).
assert (ASTK2 : astk ar M2 E SCR).
{ apply (astk_after_rt L ar C HI HIok (BX0 ++ LB) FF LK cr A M M1 M2 _ E SCR spc 512 HH ASTK MG01 PRES2); clear - SPSC SPO1 SPO2 SPO3 SLO; lia. }
assert (NCS : forall a, spc <= a < E -> ~ aclient L ar LB FF E SCR a).
{ intros a Xa Hc. destruct (aclient_cases L ar C HI LYa HIok (BX0 ++ LB) FF LK cr A M _ E SCR a HH SPT (aclient_appb L ar LB BX0 FF E SCR a Hc)) as [Y|Y].
- clear - Xa Y SPSC SPO1 SPO2 SPO3; lia.
- clear - Xa Y SLO SPSC SPO1 SPO2 SPO3; lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (BQ : ff_bytes k mod 8 = 0 /\ (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (clear - F8 B64 FR; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (NCF : forall a, (F <= a < F + ff_bytes k \/ S F <= a <= S (F + ff_bytes k - 1)) -> ~ aclient L ar LB FF E SCR a).
{ intros a Ha Hc. apply (fresh_frame_not_client L ar C HI LYa HIok (BX0 ++ LB) FF LK cr A M _ E SCR F (ff_bytes k) a HH SPT).
- clear - FR; lia.
- exact FCEIL.
- exact FAPP.
- clear - F8; lia.
- clear - FR; lia.
- exact (proj1 BQ).
- eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg.
- exact FBLK.
- exact Ha.
- exact (aclient_appb L ar LB BX0 FF E SCR a Hc). }
assert (AGF : forall a, spc <= a < E -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha. apply (proj1 PRES2 a); [clear - Ha SPSC SPO1 SPO2 SPO3 SLO SHI SPT; lia|]. apply stack_client; clear - Ha SPSC SPO1 SPO2 SPO3 SLO SHI SPT; lia. }
assert (FLNCl : ~ aclient L ar LB ((F, k, spc + 32) :: FF) 0 0 fl) by (intros X; apply FLNC; exact (aclient_appb L ar LB BX0 _ 0 0 fl X)).
assert (G : PMAUK.gctx L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0).
{ refine (PMAUK.GCTX L ar HI LB FF LK A E SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr BX0
Hk6 SPT SLO SHI _ OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNCl HH2 FLC _ _ FBIG F32 FLA FLR FLBIG NCF NCS).
- clear - SLO SHI SPT SPSC SPO1 SPO2 SPO3; lia.
- clear - FR; lia.
- split; [exact F8| exact (proj2 BQ)]. }
apply (KONT R2 M2 model2 F fl LK2 G B10 RP2 (conj Hh2 MI2) RT2 ASTK2).
+ eapply ek_trans. exact EK01. intros a (Ha & Hc & _). apply (proj1 PRES2 a Ha).
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a (aclient_appb L ar LB BX0 FF E SCR a Hc)). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ eapply dk_trans. exact DK01. intros a Ha Hc Hn. rewrite (proj1 PRES2 a Ha). exact Hn.
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a (aclient_appb L ar LB BX0 FF E SCR a Hc)). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ intros a (Ha & Hc & _). apply (proj1 PRES2 a Ha).
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a Hc). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ intros a Ha Hc Hn. rewrite (proj1 PRES2 a Ha). exact Hn.
apply (aclient_mono L ar (BX0 ++ LB) FF E SCR spc 512 a Hc). intros x Hx. clear - Hx SPSC SPO1 SPO2 SPO3; lia.
+ exact AGF.
+ exact FWv.
+ exact FSHW.
+ exact FSHZ.
+ exact FLCv.
+ exact FLWv.
+ exact FDEFv.
+ exact VF.
+ exact VSH.
+ exact VFL.
+ intros a n sp0 scr0 Hc Hn.
exact (sm_apart L ar C HI LYa HIok (BX0 ++ LB) FF LK2 cr A M2 _ F k (spc + 32) fl sp0 scr0 a n HH2 SPT Hk6 ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC Hc Hn).
Qed.

(* [comment removed for export] *)
Lemma wret_ek LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 LB6 LK6 cr6 A6 (Mx Mf : word -> option byte) V6
      (W : list L5.range) (Wx : Z -> Prop) :
  PMAUK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 ->
  ri_inv HI LB6 ((F, k, spc + 32) :: FF) LK6 cr6 A6 Mx V6 ->
  (forall a, Wx a -> ~ L5.outside W a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ PMAUK.WretX F fl k Wx a -> Mf (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB6 FF 0 0 W Mx Mf.
Proof. 
intros G HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
assert (FB8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
apply (ek_piece L ar LB6 FF 0 0 W Mx Mf (PMAUK.WretX F fl k Wx) FZ).
intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].
assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
\/ aclient L ar LB FF sp SCR a).
{ intros BS ST X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
- left; exact X.
- right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 X)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
+ clear - Y1 FCEIL X FR. lia.
+ clear - Y1 FR F8 X SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
+ subst a. clear - FLR X. lia.
- right; left. exact (proj1 X).
- right; right; right. unfold aclient, aclient_g. do 3 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 4 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 5 right; left. exact X.
- right; right; left. exact X. }
destruct (IND _ _ Hc) as [X|[X|[X|X]]].
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
+ destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
- rewrite (aly_img_lo L C LYa), (aly_img_hi L C LYa) in X. destruct Wa as [[Y|Y]|Y].
+ clear - X Y FR; lia.
+ clear - X Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. clear - X FLR; lia.
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
+ destruct FBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
* assert (E1 : (F - 1) / 8 = F / 8 - 1).
{ rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D. unfold SB in *. lia.
* assert (E1 : (F + ff_bytes k) / 8 = F / 8 + ff_bytes k / 8).
{ rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes k / 8 * 8) with ((F / 8 + ff_bytes k / 8) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_le_mono (F + ff_bytes k) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D FB8. unfold SB in *. lia.
+ subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
- destruct Wa as [[Y|Y]|Y].
+ apply (NCF a); [left; clear - Y FR; lia| exact X].
+ apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact X].
+ subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact X.
Qed.

(* [comment removed for export] *)
Definition Wfr (F fl k : Z) (Wx : Z -> Prop) (a : Z) : Prop := ((F <= a < F + ff_bytes k \/ F / 8 + SB <= a < F / 8 + SB + ff_bytes k / 8) \/ a = fl) \/ Wx a.
Lemma wfr_ek LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 LB6 LK6 cr6 A6 (Mx Mf : word -> option byte) V6
      (W : list L5.range) (Wx : Z -> Prop) :
  PMAUK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2 BX0 ->
  ri_inv HI LB6 ((F, k, spc + 32) :: FF) LK6 cr6 A6 Mx V6 ->
  (forall a, Wx a -> ~ L5.outside W a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wfr F fl k Wx a -> Mf (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB6 FF 0 0 W Mx Mf.
Proof. 
intros G HH6 WXin FZ. pose proof G as G'. destruct G' as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB & WF & FSAPP & FSCEIL & _).
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP, FSCEIL.
assert (FB8 : (F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1 /\ ff_bytes k / 8 * 8 = ff_bytes k) by (split; [exact (proj1 (proj2 F8)) | exact (proj2 (proj2 F8))]).
apply (ek_piece L ar LB6 FF 0 0 W Mx Mf (Wfr F fl k Wx) FZ).
intros a Ha Hc Ho [Wa|Wa]; [| exact (WXin a Wa Ho)].
assert (IND : forall BS ST, aclient_g BS ST L ar LB6 FF 0 0 a -> in_block LB6 a \/ (hl_img_lo L <= a < hl_img_hi L) \/ (exists b, In b LB6 /\ BS (fst b) (snd b) a)
\/ aclient L ar LB FF sp SCR a).
{ intros BS ST X. destruct X as [X|[X|[X|[X|[X|[X|X]]]]]].
- left; exact X.
- right; right; right. unfold aclient, aclient_g. right; left. split; [exact (proj1 X)|]. intros Y. destruct Wa as [[Y1|Y1]|Y1].
+ clear - Y1 FCEIL X FR. lia.
+ clear - Y1 FR F8 X SPT. unfold SB in *. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D. lia.
+ subst a. clear - FLR X. lia.
- right; left. exact (proj1 X).
- right; right; right. unfold aclient, aclient_g. do 3 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 4 right; left. exact X.
- right; right; right. unfold aclient, aclient_g. do 5 right; left. exact X.
- right; right; left. exact X. }
destruct (IND _ _ Hc) as [X|[X|[X|X]]].
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5. destruct Wa as [[Y|Y]|Y].
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; clear - Y Z Xb FR; lia.
+ destruct B5 as (_ & B5 & _). clear - Y Xb B5 FR F8. unfold SB in *.
pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)) as D. change (2 ^ 47 / 8) with 17592186044416 in D.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. unfold FS_BYTES in BFS, FLP. clear - Xb BFS FLP. lia.
- rewrite (aly_img_lo L C LYa), (aly_img_hi L C LYa) in X. destruct Wa as [[Y|Y]|Y].
+ clear - X Y FR; lia.
+ clear - X Y FR. unfold SB in *. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia.
+ subst a. clear - X FLR; lia.
-
destruct X as (b & Hb & Xb). destruct (WB b Hb) as ((B0 & B1 & B2 & B3 & B4 & B5) & _ & _ & _ & _ & FA & BFS).
unfold in_shadow_of, S in Xb. destruct Wa as [[Y|Y]|Y].
+ destruct FBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Y Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Y Z Xb D FR; lia.
+ destruct (FA (F, k, spc + 32) (or_introl eq_refl)) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z.
* assert (E1 : (F - 1) / 8 = F / 8 - 1).
{ rewrite <- (proj1 F8) at 1. replace (F / 8 * 8 - 1) with (7 + (F / 8 - 1) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
pose proof (Z.div_le_mono (fst b + snd b - 1) (F - 1) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D. unfold SB in *. lia.
* assert (E1 : (F + ff_bytes k) / 8 = F / 8 + ff_bytes k / 8).
{ rewrite <- (proj1 F8) at 1. rewrite <- (proj2 FB8) at 1. replace (F / 8 * 8 + ff_bytes k / 8 * 8) with ((F / 8 + ff_bytes k / 8) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity. }
pose proof (Z.div_le_mono (F + ff_bytes k) (fst b) 8 ltac:(lia) ltac:(clear - Z; lia)) as D. rewrite E1 in D.
clear - Y Xb D FB8. unfold SB in *. lia.
+ subst a. destruct FLBIG as [Z|Z]; unfold SB in Xb.
* pose proof (Z.div_le_mono (fst b + snd b - 1) (2 ^ 47 - 8388608) 8 ltac:(clear - B0 B3; lia) ltac:(clear - B4 SPT; lia)) as D. change ((2 ^ 47 - 8388608) / 8) with 17592184995840 in D. clear - Z Xb D; lia.
* pose proof (Z.div_pos (fst b) 8 ltac:(clear - B0; lia) ltac:(lia)) as D. clear - Z Xb D; lia.
- destruct Wa as [[Y|Y]|Y].
+ apply (NCF a); [left; clear - Y FR; lia| exact X].
+ apply (NCF a); [right; unfold S; rewrite (proj1 FB8); unfold SB in *; clear - Y; lia| exact X].
+ subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact X.
Qed.

(* [comment removed for export] *)
Lemma ahpres_of_frame_but LB FF LK cr A M M' V sp scr :
  ri_inv HI LB FF LK cr A M V -> 140735340871680 <= ar_sptop ar <= 2 ^ 47 -> ahl_ceil ar <= sp - scr -> 0 <= scr ->
  L5.frame_but [(sp - scr, scr)] M M' -> mem_grows M M' -> L5.defined M (sp - scr) scr ->
  ahpres L ar LB FF sp scr [] M M'.
Proof. 
intros HH SPT HC HS FB MG D. split; [|split].
- intros a (Ha & Hc & _). apply FB. rewrite L5.unsigned_lit by lia.
destruct (aclient_cases L ar C HI LYa HIok LB FF LK cr A M V sp scr a HH SPT Hc) as [(Y1 & Y2)|Y].
+ intros r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply Y2. lia.
+ intros r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
- apply (L5.defined_grows M M' _ _ MG D).
- intros a Ha Hc Hn. exact (MG _ Hn).
Qed.
End WithIface.
End SCFG_1.
End PMAUAR.
