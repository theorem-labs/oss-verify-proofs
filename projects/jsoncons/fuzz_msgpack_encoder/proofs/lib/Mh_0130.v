(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed SEALED_BYTES_length, SEALED_BYTES_nth_hi, SEALED_W_bytes and 119 more; added rz; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/SegRun.v at theorem-labs/oss-verify-proofs@f92feaf8b7e6, 667 lines within its lines 49-1436. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From Stdlib Require FunctionalExtensionality. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0130 () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List6map_idC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02I45stdpp9bitvector;definitions2bv00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03I46Stdlib9micromega7EnvRing5PExpr00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8sr_freshC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8fresh_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<maps_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_ghostC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_01128AsanPlan2AP=pairs_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:fd_vars_ltC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9ext_call2C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;after_call2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS2MrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8a_tidsetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP3acs01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@w_fresh_ok_partsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?ext_call2_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib=AsanPlanSound3APS?sr_vars_lt_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@sr_vars_lt_freshC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8ext_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAext_call2_agree16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APSAexpr_vars_lt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>sr_vars_lt_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS7co_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?regs_after_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>regs_ok_agree'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>w_env_agree_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9call_coreC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7with_ssC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z7inj_addC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI69OSSVerify5KrLib7Mh_01128AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib7Mh_01128AsanPlan2AP3NCSC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<caller_savedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00C46Stdlib5Lists4List2Inc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=nth_repeat_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC47Corelib4Init5Logic3iffI46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula02C47Corelib4Init5Logic8iff_reflK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib9micromega:ZMicromega=Zeval_formulaK46Stdlib9micromega7EnvRing5PExpr07K45stdpp9bitvector;definitions2bv01C46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9copy_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib7Mh_01128AsanPlan2AP7ret_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:after_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;off_image_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kzero_xC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8kn_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6flat_xC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC69OSSVerify5KrLib7Mh_01128AsanPlan2AP:copy_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS6alwaysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<summary_copyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS7co_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP@summary_copy_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?summary_copy_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;w_reg_soundC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib7Mh_01128AsanPlan2AP;kwritable_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S5elenZC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<kblob_prefixC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=ret_lit_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xlo_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xhi_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAw_split_lit_denotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?call_node_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8k0_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAkwritable_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SDranges_apart_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?w_know_ok_havocC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?nth_sr_vars_lt'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>split_lit_varsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>w_flat_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<store_ok_rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22ebC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=edenot_agree'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List:in_map_iffC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions7bv_wrapC47Corelib4Init3Nat3subK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses6eq_iffC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9rdn_skipnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9mod_smallC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXKword_to_le_bytes_of_bytes_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<ext_call2_atC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9adenot_SAC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:edenot_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7rdn_nthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:wbytes_nthC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_agree'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>wbytes_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SDknow_ok_unk_intro_ptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@call_node_sound2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=kzero_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?rdn_overlay_allC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>wbytes_fill_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26zlit64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_lit64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9zlit64_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@copy_facts_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS:node1_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses5mkappC69OSSVerify5KrLib7Mh_01128AsanPlan2AP8kimg_cutC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib5Lists7ListDef6Forall01K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_minI46Stdlib5Lists4List6Exists00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Module AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPopFree.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPlanSoundSums () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List6map_idC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24ridxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C46Stdlib5Lists4List2InK46Stdlib9micromega6VarMap1t01K46Stdlib5Lists4List5NoDup01I46Stdlib5Lists4List5NoDup00K46Stdlib5Lists4List5NoDup02C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<caller_savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8sr_freshC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:nth_sr_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC47Corelib4Init5Peano2ltC47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib5Arith8PeanoNat3Nat8eqb_reflc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@nth_sr_fresh_outC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses6mkapp2C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8ext_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22ebC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8leb_specI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init3Nat3subK47Corelib4Init5Logic3and01C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib7Mh_01128AsanPlan2AP3NCSC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6leb_leC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init9Datatypes?andb_true_introC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC69OSSVerify5KrLib7Mh_01128AsanPlan2AP:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC46Stdlib5Lists4List6In_nthI47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>ext_call_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?nth_sr_vars_lt'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=edenot_agree'C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:ridx_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;reg_of_ridxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<ext_call_varC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?nth_sr_fresh_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAregs_ok_pointwiseC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXBcaller_saved_nodupC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec8Z_lt_decC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:wbytes_outC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:wbytes_nthC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK46Stdlib9micromega5Tauto8GFormula07C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z7add_0_rC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List9seq_shiftC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAland_shl_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC49OSSVerify5KrLib8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@lor_shl_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z6shiftrC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib?AxSymExec3Sound4AX2SCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXFZ_to_le_bytes_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXIword_to_le_bytes_of_bytesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kwritableC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S5elenZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib?AxSymExec3Sound4AX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xlo_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib?AxSymExec3Sound4AX2S=xinside_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27xinsideC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;kwritable_xC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xhi_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kzero_xC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List?Forall_flat_mapC69OSSVerify5KrLib7Mh_01128AsanPlan2AP9kimg_cut1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes3appC46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8kimg_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:Forall_oneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;know_lookupC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SAknow_lookup_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S8sc_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8piece_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9adenot_SAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4extzC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28sidecond00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7kread8eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<lookup_pieceC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24lres03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6kreadZC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC49OSSVerify5KrLib8PropExec?bytes_le_singleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_lit64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions=bv_wrap_smallK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;kread_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<kreadZ1_byteC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions?bv_add_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec7rdn_appC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2>zbytes_le_to_ZC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:zbytes_mapC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List;firstn_all2C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:copy_factsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9rdn_skipnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=kread8e_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAkread_bytes_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?zbytes_of_smallC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib=AsanPlanSound3APS5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS9reg_soundC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP3acs00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7reg_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=reg_lit_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS?split_lit_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=know_ok_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6flat_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS<flat_x_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8fresh_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS;cs_ok_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=pairs_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS9hid_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS6allowAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS;cs_ok_frameC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=lazy_cover_csC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_01128AsanPlan2AP6spiece00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS;A_wf_allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APSAH_off_segments_csC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>fresh_ok_partsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?find_segment_InC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4to_Nc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9wview_rd1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP2pcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7with_ssC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib=AsanPlanSound3APS6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@w_fresh_ok_partsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<maps_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP4a_fdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXCw_H_off_segments_csC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?w_lazy_cover_csC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=w_A_wf_allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS7co_haltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct=restrict_mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=w_cs_ok_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;w_hid_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS<allowA_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APSKmrestrict_munrestrict_cleanC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=w_cs_ok_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:fd_vars_ltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC59OSSVerify5KrLib=AsanPlanSound3APS>sr_vars_lt_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:after_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8a_tidsetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP3acs01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS7co_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?regs_after_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_agree'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>w_env_agree_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9call_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS8ext_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>ext_list_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9ext_call2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS;ext_list_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7ret_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP3regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;w_reg_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C46Stdlib5Lists4List9nth_indepC46Stdlib5Lists4List7map_nthC46Stdlib5Lists4List7seq_nthC46Stdlib5Lists4List:length_seqc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;nth_map_seqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=nth_repeat_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;off_image_xC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>kimg_cut_soundC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z7mod_modc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9fill_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS6alwaysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<summary_fillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS7co_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP@summary_fill_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?summary_fill_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib7Mh_01128AsanPlan2AP8kn_havocC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=ret_lit_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?w_reg_lit_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAw_split_lit_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?call_node_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAkwritable_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=kzero_x_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<Z_to_bv8_modC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;wbytes_sameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8k0_soundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?w_know_ok_havocC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>wbytes_fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS:node1_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;x_memiszeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8miz_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP;summary_mizC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?summary_miz_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP>summary_miz_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP5eaddzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkAluC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkAlu_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?kwritable_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SDranges_apart_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<rdn1_overlayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP7img_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC47Corelib7Classes?RelationClasses;reflexivityC47Corelib7Classes?RelationClassesBPreOrder_Reflexivec69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXKword_to_le_bytes_of_bytes_nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<SEALED_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8SEALED_WC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;le_preorderC46Stdlib5Lists4List8app_nth2C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:x_istrncpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8x_sealedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=istrncpy_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP@summary_istrncpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2APDsummary_istrncpy_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2APCsummary_istrncpy_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS9elenZ_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=img_cov_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX:rdn_of_nthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXCSEALED_BYTES_nth_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXCSEALED_BYTES_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6u_lit0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>SEALED_W_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List9nth_skipnC46Stdlib5Lists4List;skipn_skipnc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXDfirstn_skipn_map_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List6in_seqC59OSSVerify5KrLib7Mh_0112;AsanPopFree8pf_bytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib7Mh_0112;AsanPopFree?pf_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib7Mh_0112;AsanPopFree=pf_bytes_cellC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0112;AsanPopFreeCword_to_le_bytes4_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP=popfree_factsC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC69OSSVerify5KrLib7Mh_01128AsanPlan2AP9x_popfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0112;AsanPopFree<popfree_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP?summary_popfreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC2pcC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3addC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC4a_ssC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3subC57Corelib7BinNums6IntDef1Z3mulC57Corelib7BinNums6IntDef1Z3divC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3regC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3oppC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5eaddzC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z6to_natC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC=popfree_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8kn_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC7with_ssC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7mod_addC59OSSVerify5KrLib?AxSymExec3Sound4AX2S7u_add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>env_agree_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC56Stdlib5Arith8PeanoNat3Nat7eqb_neqc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXCpopfree_facts_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>wbytes_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S@Forall_app_introC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3acs00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9x_imemsetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXBsummary_fill_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS6x_stmtC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8x_memsetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP9x_imemcpyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9copy_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXBsummary_copy_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP8x_memcpyC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAsummary_miz_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode05C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXFsummary_istrncpy_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode09C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXEsummary_popfree_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_01128AsanPlan2AP5xnode0:C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

Section Specs.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
(* [comment removed for export] *)
Definition fill_spec (entry cmax : Z) : Prop :=
  forall mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
    0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    bv_unsigned c < cmax ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = s.

(* [comment removed for export] *)
Definition copy_spec (entry : Z) : Prop :=
  forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn SEGS mem0 src (length bs) = Some bs ->
    store_ok SEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
Definition miz_spec (entry : Z) : Prop :=
  forall mem (beg sp : word) (N : Z) (regs : bvmap 5 word) (ret : word),
    0 <= N <= 2 ^ 40 -> bv_unsigned beg + N + 8 <= 2 ^ 64 -> 16 <= bv_unsigned sp ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
    (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg) ->
    (forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
       rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
    getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 1.

(* [comment removed for export] *)
Definition SEALED_BYTES : list byte :=
  [Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]
  ++ repeat (Z_to_bv 8 0) 4087.

(* [comment removed for export] *)
Definition istrncpy_spec (entry src : Z) : Prop :=
  forall mem0 (dst : word) (regs : bvmap 5 word) (ret : word),
    (forall i, src <= i < src + 9 -> mem0 (Z_to_bv 64 i) = None) ->
    store_ok SEGS mem0 dst 4095%nat = true ->
    bv_unsigned dst + 4095 < 2 ^ 64 ->
    (bv_unsigned dst + 4095 <= src \/ src + 9 <= bv_unsigned dst) ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = Z_to_bv 64 src -> getr regs 12%bv = Z_to_bv 64 4095 ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => AP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_same : forall bs m (a : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, (j < length bs)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  wbytes m a bs = m.
Proof.
  intros bs m a Hnw Hall. apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { apply wbytes_out; [exact Hnw | lia]. }
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
  2: { apply wbytes_out; [exact Hnw | lia]. }
  set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
  assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  { subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined : forall bs m (a : word) j,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_all : forall segs m n (a : word) b,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (bv_unsigned a + i)) = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat].
  pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_nth : forall segs m n (a : word) bs j,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs m a n = Some bs -> (j < n)%nat ->
  rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
  - cbn [nth]. destruct n as [|n'']; [lia|].
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
    apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
  rdn segs m a n = Some (map f (seq 0 n)).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs,
  (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
  length bs = n -> (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KnowTests.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable] in H.
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
  { intros A B. split; [|lia].
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
  lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
    pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
  - lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
    apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
    apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
    destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
    unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
    unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable_x allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kzero_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kzero_x allkn k b off n = true ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 (estart E (SA b off))) w = Some bs /\ length bs = w
             /\ word_to_le_bytes w (edenot E v) = bs.

Lemma lookup_piece : forall E M k b off w v hs,
  know_ok segs E M k -> (1 <= w <= 8)%nat ->
  know_lookup segs k b off w false [] [] = LHit v [] hs ->
  flat E (SA b off) (Z.of_nat w) ->
  piece_ok E M b off w v.
Proof.
  intros E M k b off w v hs HK Hw HL Hfl.
  pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
  unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

Lemma kread8e_piece : forall E M k b off v,
  know_ok segs E M k -> kread8e segs k b off = Some v -> flat E (SA b off) 8 ->
  piece_ok E M b off 8 v.
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

Lemma kreadZ1_byte : forall E M k b off z,
  know_ok segs E M k -> kreadZ segs k b off 1 = Some z -> flat E (SA b off) 1 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) 1 = Some [Z_to_bv 8 z] /\ 0 <= z < 256.
Proof.
  intros E M k b off z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  destruct bs as [|b0 [|]]; try discriminate.
  cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
  pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
  split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma kread_bytes_sound : forall E M k len b off zs,
  know_ok segs E M k -> kread_bytes segs len k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat len <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) len = Some (map (fun z => Z_to_bv 8 z) zs)
  /\ length zs = len /\ Forall (fun z => 0 <= z < 256) zs.
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
  - cbn [kread_bytes] in H.
    destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
    destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
    destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
    split; [| split; [cbn; lia | constructor; assumption]].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
    apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma zbytes_of_small : forall zs, Forall (fun z => 0 <= z < 256) zs ->
  zbytes_le_to_Z zs = bytes_le_to_Z (map (fun z => Z_to_bv 8 z) zs).
Proof.
  intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
  induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_facts_sound : forall E M k sb db fuel sk dk n kc,
  know_ok segs E M k ->
  copy_facts segs fuel k sb sk db dk n = Some kc -> 0 <= n -> (Z.to_nat n <= fuel)%nat ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + n <= 2 ^ 64 ->
  0 <= estart E (SA db dk) -> estart E (SA db dk) + n <= 2 ^ 64 ->
  exists bs, length bs = Z.to_nat n
    /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
    /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc.
Proof.
  intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
  - cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
    exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
  - cbn [copy_facts] in H.
    (* common step: a w-byte piece then the rest *)
    assert (STEP : forall (w : nat) v kr,
      (1 <= w <= 8)%nat -> Z.of_nat w <= n ->
      piece_ok E M sb sk w v ->
      copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
      kc = KWord (SA db dk) w v :: kr ->
      exists bs, length bs = Z.to_nat n
        /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
        /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
    { intros w v kr Hw Hwn (bsP & HrdP & HlenP & HvP) Hr ->.
      assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
        as (bsR & HlenR & HrdR & HKR).
      exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
      - replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
        apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
        rewrite ES in HrdR.
        replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
      - intros M' HM'. constructor.
        + cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
          rewrite adenot_SA, HvP.
          pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
          rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
        + apply HKR. rewrite ED.
          pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
          replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
          replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
          rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
    + apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
      destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
        [|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
      assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
      destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
      * injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
      * destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
        apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
        destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
        exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
        cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
        replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
        apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
    + clear H8. destruct (Z.leb 1 n) eqn:H1.
      * apply Z.leb_le in H1.
        destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
        destruct scs; [|discriminate].
        destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
        injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
      * injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
        exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable rz : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
(* [comment removed for export] *)
Variable FS0 : Fs.Fs.
(* [comment removed for export] *)
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A argH) (only parsing).
#[local] Notation MR := (Mr A argH) (only parsing).

(* [comment removed for export] *)
#[local] Ltac aps_fill :=
  first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
        | exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT].

Lemma w_reg_sound : forall E cs R FULL model n,
  CSOK E cs R FULL model -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_reg_lit_sound : forall E cs R FULL model n z,
  CSOK E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ 0 <= z < two64.
Proof. intros. eapply reg_lit_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. eapply split_lit_denot; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_know_ok_havoc : forall E M M' k b o n,
  know_ok SEGS E M k ->
  (forall x : word, bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x -> M' x = M x) ->
  mem_grows M M' ->
  know_ok SEGS E M' (kn_havoc k b o n).
Proof. intros. eapply know_ok_havoc; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_flat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> flat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof. intros. eapply flat_x_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [Hv Hb] Hle. split; [|exact Hb]. intros n Hn. apply Hv. lia. Qed.

Lemma w_cs_ok_agree : forall E E' cs R FULL model,
  env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> CSOK E cs R FULL model -> CSOK E' cs R FULL model.
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_hid_agree : forall b E E' cs model,
  env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
  HID E' cs model = HID E cs model.
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
  CSOK E cs R FULL model -> same_but_materialized model model' -> MInv (allowA A E cs) model' ->
  regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
  know_ok SEGS E (MR E cs model FULL') (s_know ss') ->
  (forall a, HID E cs model a = true -> FULL' a = FULL a) ->
  CSOK E (with_ss cs ss') R' FULL' model'.
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_lazy_cover_cs : forall E cs R FULL model,
  CSOK E cs R FULL model -> lazy_cover (HID E cs model) (m_vm_lazy model) (allowA A E cs).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
  AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.

(* [comment removed for export] *)

Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma wview_rd1 : forall M (a : word) b,
  wview SEGS M a = Some b ->
  (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
  intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (seg_writable seg) eqn:Hw; [|discriminate].
  rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.

Lemma store_ok_rdn : forall n M (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  exists bs, rdn SEGS M a n = Some bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros M a Hnw Hst.
  - exists []. split; reflexivity.
  - cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
    cbn [rdn]. rewrite (wview_rd1 M a b Hv).
    destruct n as [|n'].
    + exists [b]. split; reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
      rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma call_core : forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
  CSOK E cs R FULL model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' MR' k' ->
  (forall R' FULL' model',
      CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' ret FULL' model') T) ->
  srealizes SEGS scfg (cfg R (pc cs) FULL model) T.
Proof.
  intros cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (H := HID E cs model).
  unfold cfg_of.
  apply (srz_msteps_restricted_T SEGS scfg H
           (w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
           (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
           (w_lazy_cover_cs E cs R FULL model HC)
           (w_A_wf_allowA E cs)
           (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC)).
  - rewrite restrict_mkst. exact Hms.
  - intros model' Hinv' Hsame Hclean.
    set (FULL' := munrestrict H FULL MR').
    change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
      with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
    apply (Hk regs' FULL' model').
    + pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
      pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
      eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
      * rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
      * exact HR'.
      * reflexivity.
      * cbn [s_know mk_ss]. unfold Mr. rewrite HH.
        fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
        exact HK'.
      * intros a Ha. rewrite HH in Ha.
        unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
    + apply (same_but_materialized_frame _ _ Hsame).
Qed.

Lemma sr_vars_lt_fresh : forall rs sr nx b,
  AP.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> AP.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
  induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
  apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma call_node_sound : forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
  CSOK E cs R FULL model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS scfg (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
    split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
  ext_list (ext_call E nx R') (nx + NCS) vals.

Lemma ext_call2_agree : forall E nx R' vals, env_agree nx E (ext_call2 E nx R' vals).
Proof.
  intros E nx R' vals. unfold ext_call2.
  destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
  split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.

Lemma ext_call2_agree16 : forall E nx R' vals, env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals).
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.

Lemma ext_call2_at : forall E nx R' vals i, (i < length vals)%nat ->
  ev (ext_call2 E nx R' vals) (nx + NCS + i) = nth i vals (Z_to_bv 64 0).
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.

Lemma call_node_sound2 : forall cs cs' E R FULL model T (ret : Z) rv k' extra vals regs' MR',
  CSOK E cs R FULL model ->
  after_call2 nx0 cs ret rv k' extra = Some cs' ->
  msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
              (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k' ->
  (forall E' R' FULL' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS scfg (cfg R' (pc cs') FULL' model') T) ->
  srealizes SEGS scfg (cfg R (pc cs) FULL model) T.
Proof.
  intros cs cs' E R FULL model T ret rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
  unfold after_call2 in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call2 E (nxt cs) regs' vals).
  pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
  set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
  assert (Hsf : AP.sr_vars_lt (nxt cs + NCS) sr1 = true).
  { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
    unfold caller_saved, NCS. cbn [length]. lia. }
  assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
  { eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
    - destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
    - subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
      destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
  eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK').
  intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
  split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ret_lit_sound : forall E cs R FULL model r,
  CSOK E cs R FULL model -> ret_lit cs = Some r ->
  getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64.
Proof.
  intros E cs R FULL model r HC H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (w_reg_sound E cs R FULL model 1 HC ltac:(lia)) as R1.
  rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.


Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> AP.expr_vars_lt m e = true -> AP.expr_vars_lt m b = true.
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

(* [comment removed for export] *)
Lemma k0_sound : forall E M k db dk ne dst k0,
  know_ok SEGS E M k ->
  (if off_image_x A k db dk ne then Some k
   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
  know_ok SEGS E M k0.
Proof.
  intros E M k db dk ne dst k0 HK H.
  destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
  destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
  apply kimg_cut_sound. exact HK.
Qed.

(* [comment removed for export] *)
Lemma wbytes_fill_at : forall M (s : word) b n i,
  bv_unsigned s + n <= 2 ^ 64 -> 0 <= i < n ->
  wbytes M s (repeat b (Z.to_nat n)) (Z_to_bv 64 (bv_unsigned s + i)) = Some b.
Proof.
  intros M s b n i Hnw Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof.
  intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
Lemma summary_fill_sound : forall entry cmax,
  fill_spec SEGS entry cmax ->
  node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (fun cs => summary_fill A nx0 cs entry cmax).
Proof.
  intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_fill_eq in Hn. (* [comment removed for export] *) unfold summary_fill_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
  destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k',
     store_ok SEGS M s (Z.to_nat n) = true ->
     know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
  { intros k' Hst HK' Hac.
    destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
      as (regs' & Hms & Hkept & Ha0).
    rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
  assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
  { apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
    rewrite Hse, Hlen in *.
    apply (FIN (kn cs)); [apply Wst; lia | | exact Hn].
    destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
    rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
  clear Hzb.
  (* [comment removed for export] *)
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
  destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite Hse, Hlen in *.
  eapply FIN; [apply Wst; lia | | exact Hn].
  set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
  assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
  { eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    subst M'. apply wbytes_out; rewrite repeat_length; lia. }
  destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
  assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
  assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
  { intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
  constructor; [|exact HK1].
  destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
  - apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
  - split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma store_ok_sub : forall M (a : word) n (b : word) m,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  bv_unsigned a <= bv_unsigned b -> bv_unsigned b + Z.of_nat m <= bv_unsigned a + Z.of_nat n ->
  store_ok SEGS M b m = true.
Proof.
  intros M a n b m Hnw Hst Hlo Hhi. apply store_ok_of_all; [lia|].
  intros x Hx. eapply (store_ok_all SEGS M n a Hnw Hst). lia.
Qed.

Lemma summary_miz_sound :
  miz_spec SEGS (x_memiszero A) ->
  node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (fun cs => summary_miz A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_miz_eq in Hn. (* [comment removed for export] *) unfold summary_miz_ref in Hn.
  destruct (Z.eqb (pc cs) (x_memiszero A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eaddz (reg cs 2) (-16))) as [qb qk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hap].
  apply andb_prop in Hcond as [Hcond Hwr]. apply andb_prop in Hcond as [Hcond Hsphi'].
  apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hb8].
  apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.leb_le in Hb8. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'.
  unfold two64 in Hb8, Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (beg := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *.
  set (nw := edenot E (reg cs 11)) in *. set (N := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold N in Hnr. pose proof (u64_range beg) as Hbr. pose proof (u64_range spw) as Hsr.
  assert (HnwN : Z_to_bv 64 N = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HlenN : elenZ E (reg cs 11) = N) by reflexivity.
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = bv_unsigned spw - 16).
  { apply (f_equal bv_unsigned) in Hq. rewrite !u_lit64 in Hq. unfold two64 in Hq.
    change (estart E (SA qb qk)) with Q in Hq.
    rewrite (Z.mod_small Q) in Hq by lia.
    rewrite <- Hq.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  assert (Hstk : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 8)) 8 = true).
  { apply (store_ok_sub M (Z_to_bv 64 Q) 16); rewrite ?u64_lit by lia; try lia. exact Qst. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold beg in Hbeg.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz) as (Zb & Blo & Bhi).
  rewrite HlenN in Zb, Bhi.
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) qb qk (ELit 16) bb bk (reg cs 11) HKN Hap) as Hapart.
  rewrite HlenN in Hapart. change (estart E (SA qb qk)) with Q in Hapart.
  replace (elenZ E (ELit 16)) with 16 in Hapart by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  set (B := estart E (SA bb bk)) in *.
  assert (HuB : bv_unsigned beg = B \/ (B = 2 ^ 64 /\ bv_unsigned beg = 0)).
  { destruct (Z.eq_dec B (2 ^ 64)) as [HB|HB].
    - right. split; [exact HB|]. rewrite Hbeg. change (bv_unsigned (edenot E bb) + bk) with B. rewrite HB. reflexivity.
    - left. rewrite Hbeg. apply u64_lit. lia. }
  assert (Hdisj : bv_unsigned beg + N <= bv_unsigned spw - 8 \/ bv_unsigned spw <= bv_unsigned beg) by lia.
  assert (Hz : forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
                 rdn SEGS M a 1 = Some [Z_to_bv 8 0]).
  { intros a Ha. apply rdn1_overlay.
    destruct HuB as [HuB|[HB Hu0]]; [|lia].
    replace a with (Z_to_bv 64 (B + (bv_unsigned a - B))) by (rewrite <- (Z_to_bv_bv_unsigned 64 a) at 2; f_equal; lia).
    apply Zb. lia. }
  destruct (SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
               ltac:(rewrite HnwN; exact R11)) as (regs' & Hms & Hkept & Ha0).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (ELit 1)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 16)) with 16 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

Lemma summary_copy_sound : forall entry,
  copy_spec SEGS entry ->
  node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (fun cs => summary_copy SEGS A nx0 cs entry).
Proof.
  intros entry SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_copy_eq in Hn. (* [comment removed for export] *) unfold summary_copy_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (w_split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
  assert (Hlen : elenZ E ne = n) by reflexivity.
  (* [comment removed for export] *)
  assert (FIN : forall k' bs,
     length bs = Z.to_nat n ->
     rdn SEGS M sr (length bs) = Some bs ->
     store_ok SEGS M s (length bs) = true ->
     (bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
     know_ok SEGS E (wbytes M s bs) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
  { intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
    destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
  apply andb_prop in Hwa as [Hwr Hap].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  rewrite Hse in Wst.
  (* [comment removed for export] *)
  assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
            know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
  { intros bs Hlbs Hpos.
    assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
    eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
    apply wbytes_out; rewrite Hlbs; lia. }
  (* [comment removed for export] *)
  assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
  { intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
  (* [comment removed for export] *)
  assert (VARS : fresh_ok nx0 cs = true ->
            AP.kn_vars_lt (nxt cs) (kn cs) = true /\ AP.expr_vars_lt (nxt cs) db = true /\ AP.expr_vars_lt (nxt cs) ne = true
            /\ AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
  { intros Hfresh. destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _).
    split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
    eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
    forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
    after_call2 nx0 cs ret (Some (reg cs 10))
      (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
       ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
      = Some cs' ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
  { intros Hswr Hsfl W u HW Hu Hac.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
    destruct (w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos).
    rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
    change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
    destruct (HusD Spos Slo Shi) as [Hus Husr].
    destruct (store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs).
    assert (Hfresh : fresh_ok nx0 cs = true).
    { unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
    destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr).
    destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
    eapply (call_node_sound2 cs cs' E R FULL model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
    - rewrite Hpc. exact Hms.
    - exact Hkept.
    - exact Ha0.
    - set (E2 := ext_call2 E (nxt cs) regs' vals).
      pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
      assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
      assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
      assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
      assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
      pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
      apply Forall_app. split.
      + (* [comment removed for export] *)
        apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
        assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
        { unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
        cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
        rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
        subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
        assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
        rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
        pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
        pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
        replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
        rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
      + apply Forall_app. split.
        { (* [comment removed for export] *)
          unfold kblob_prefix.
          destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
          apply find_some in HF as [HinK HKt].
          destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
          apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
          apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
          pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
          assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes).
          change (estart E (SA sb sk)) with S in Bflat, Bbytes.
          destruct Hag2 as [Hag2a Heb2].
          assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
            [| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
          cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
          refine (conj _ (conj Blen _)).
          - unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
            change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
          - intros i Hi. rewrite <- Hus.
            replace i with (Z.of_nat (Z.to_nat i)) by lia.
            rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
            f_equal.
            pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
            rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
            cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
          }
      (* [comment removed for export] *)
        assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
        pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
        assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
        { eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
          intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
        destruct u; [|exact HAV2].
        constructor; [|exact HAV2].
        (* [comment removed for export] *)
        apply know_ok_unk_intro_pt.
        * unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
        * intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
          replace i with (Z.of_nat (Z.to_nat i)) by lia.
          apply wbytes_defined; rewrite Hlbs; lia.
    - exact Hk. }
  (* [comment removed for export] *)
  assert (HSRC :
    (if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
     then after_call2 nx0 cs ret (Some (reg cs 10))
            (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
                 (seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
             ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
            (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
     else None) = Some cs' ->
    srealizes SEGS scfg (cfg R (pc cs) FULL model) T).
  { destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
    apply andb_prop in Hsw as [Hswr Hsfl].
    assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
    destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
    - apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
      apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
      apply (GEN Hswr Hsfl); [|exact Hu].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - apply (GEN Hswr Hsfl); [lia | exact Hu]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
  { apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
    rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
    destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
    apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
      [apply repeat_length | | | lia | | exact Hn].
    - rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
    - rewrite repeat_length. apply Wst. lia.
    - constructor; [| apply HAVOC; [apply repeat_length | lia]].
      cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
      intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
  clear Hzs.
  (* [comment removed for export] *)
  destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
  apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
  destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
  assert (Hnn : n = nhi).
  { cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
  destruct (w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos).
  change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
  destruct (HusD Spos Slo Shi) as [Hus Husr].
  destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
    as (bs & Hlbs & Hrd & HKC).
  change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
  rewrite <- Hnn in Hlbs, Hrd, HKC.
  apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
  - rewrite Hlbs, <- Hsre. exact Hrd.
  - rewrite Hlbs. apply Wst. lia.
  - apply Forall_app. split.
    + apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
    + apply HAVOC; [exact Hlbs | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma img_cov_sound : forall E M k a b,
  know_ok SEGS E M k -> img_cov k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
  destruct K as [| | |lo hi| | | | | |]; try discriminate.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
  apply HK1. lia.
Qed.

Lemma SEALED_BYTES_length : length SEALED_BYTES = 4095%nat.
Proof. reflexivity. Qed.

Lemma SEALED_W_bytes : word_to_le_bytes 8 (Z_to_bv 64 SEALED_W) = firstn 8 SEALED_BYTES.
Proof.
  replace SEALED_W with (bytes_le_to_Z (firstn 8 SEALED_BYTES)) by (vm_compute; reflexivity).
  apply word_to_le_bytes_of_bytes_n; reflexivity.
Qed.

Lemma SEALED_BYTES_nth_hi : forall j, (8 <= j < 4095)%nat -> nth j SEALED_BYTES (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros j Hj. unfold SEALED_BYTES. rewrite app_nth2 by (cbn; lia). cbn [length]. apply nth_repeat_lt. lia.
Qed.

Lemma summary_istrncpy_sound :
  istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) ->
  node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (fun cs => summary_istrncpy A nx0 cs).
Proof.
  intros SUM cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  rewrite summary_istrncpy_eq in Hn. (* [comment removed for export] *) unfold summary_istrncpy_ref in Hn.
  destruct (Z.eqb (pc cs) (x_istrncpy A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [src|] eqn:H11; [|discriminate].
  destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate].
  destruct (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool eqn:Hsn; [|discriminate]. cbn [negb] in Hn.
  apply andb_prop in Hsn as [Hsrc Hn95]. apply Z.eqb_eq in Hsrc. apply Z.eqb_eq in Hn95. subst src n.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  rename Hcond into Hb. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  match goal with Hl : Z.leb 0 (x_sealed A) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hs0 end.
  match goal with Hl : Z.ltb (x_sealed A + 9) two64 = true |- _ => apply Z.ltb_lt in Hl; unfold two64 in Hl; rename Hl into Hs9 end.
  match goal with Hl : kwritable_x _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
  match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
  match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  destruct (w_reg_lit_sound E cs R FULL model 11 _ HC ltac:(lia) H11) as [R11 _].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *.
  pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  pose proof (k0_sound E M (kn cs) db dk (ELit 4095) (reg cs 10) k0 HKN
                ltac:(destruct (off_image_x A (kn cs) db dk (ELit 4095)); [exact Hk0 | destruct (reg cs 10); try discriminate; exact Hk0])) as HK0.
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9) HKN Hap) as Hapart.
  rewrite !elenZ_lit in * by lia.
  unfold estart in Hapart at 2 3; cbn [a_base a_off edenot] in Hapart. rewrite u_lit0 in Hapart.
  set (D := estart E (SA db dk)) in *.
  assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
  pose proof (img_cov_sound E M k0 _ _ HK0 Hcov) as Hnone.
  destruct (SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
               Hrok R1 R10 R11 R12) as (regs' & Hms & Hkept & Ha0).
  eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' _ HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - exact Ha0.
  - set (M' := wbytes M s SEALED_BYTES).
    assert (Hlen : bv_unsigned s + Z.of_nat (length SEALED_BYTES) <= 2 ^ 64) by (rewrite SEALED_BYTES_length; lia).
    assert (BY : forall j, (j < 4095)%nat -> M' (Z_to_bv 64 (D + Z.of_nat j)) = Some (nth j SEALED_BYTES (Z_to_bv 8 0))).
    { intros j Hj. subst M'. rewrite <- Hus. apply wbytes_nth; [exact Hlen | rewrite SEALED_BYTES_length; exact Hj]. }
    constructor; [|constructor].
    + (* [comment removed for export] *)
      cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
      rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
      cbn [edenot]. rewrite SEALED_W_bytes.
      replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
      apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
    + (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite elenZ_lit by lia.
      assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
      rewrite HD8. split; [unfold flat; lia|].
      intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
      rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
    + (* [comment removed for export] *)
      eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
  - exact Hk.
Qed.

(* [comment removed for export] *)

Lemma firstn_skipn_map_nth : forall {T} (d : T) k (l : list T) m, (m + k <= length l)%nat ->
  firstn k (skipn m l) = map (fun q => nth (m + q)%nat l d) (seq 0 k).
Proof.
  intros T d k. induction k as [|k IH]; intros l m Hm; [reflexivity|].
  cbn [seq map]. rewrite <- seq_shift, map_map.
  destruct (skipn m l) as [|x rest] eqn:Hs.
  - exfalso. pose proof (f_equal (@length _) Hs) as HL. rewrite length_skipn in HL. cbn in HL. lia.
  - cbn [firstn]. f_equal.
    + rewrite <- nth_skipn, Hs. reflexivity.
    + replace rest with (skipn (S m) l).
      2: { replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
      rewrite (IH l (S m)) by lia. apply map_ext. intros q. f_equal. lia.
Qed.

Lemma popfree_facts_sound : forall E M lb lk cnt c s K (base : word),
  bv_unsigned base = estart E (SA lb lk) ->
  (K <= Z.to_nat cnt)%nat -> 0 < cnt -> estart E (SA lb lk) + 4 * cnt <= 2 ^ 64 -> 0 <= estart E (SA lb lk) ->
  know_ok SEGS E (wbytes M base (pf_bytes c s (Z.to_nat cnt))) (popfree_facts lb lk cnt c s K).
Proof.
  intros E M lb lk cnt c s K base Hbase HK Hcnt Hhi Hlo. unfold popfree_facts. apply Forall_forall. intros Kx Hin.
  apply in_map_iff in Hin as [t [<- Hint]]. apply in_seq in Hint.
  set (D := estart E (SA lb lk)) in *. set (j := cnt - 1 - Z.of_nat t).
  assert (Hj : 0 <= j < cnt) by lia.
  cbn [kentry_ok]. split; [lia|].
  assert (HDj : estart E (SA lb (lk + 4 * j)) = D + 4 * j) by (unfold D, estart; cbn [a_base a_off]; lia).
  split; [unfold flat; rewrite HDj; cbn [Z.of_nat]; lia|].
  rewrite adenot_SA, HDj. cbn [edenot].
  rewrite word_to_le_bytes4_Z.
  replace ((c + Z.of_nat t * s) / 16) with ((c + (Z.of_nat (Z.to_nat cnt) - 1 - j) * s) / 16) by (f_equal; f_equal; lia).
  rewrite <- (pf_bytes_cell c s (Z.to_nat cnt) j) by lia.
  assert (Hlen : length (pf_bytes c s (Z.to_nat cnt)) = (4 * Z.to_nat cnt)%nat) by apply pf_bytes_length.
  rewrite (firstn_skipn_map_nth (Z_to_bv 8 0) 4) by (rewrite Hlen; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 (D + 4 * j)) = D + 4 * j) by (apply u64_lit; lia).
  apply rdn_of_nth; [rewrite Hu; lia|]. intros q Hq. apply rdn1_overlay. rewrite Hu.
  replace (D + 4 * j + Z.of_nat q) with (bv_unsigned base + Z.of_nat (Z.to_nat (4 * j) + q)) by lia.
  apply wbytes_nth; rewrite Hlen; lia.
Qed.

Lemma summary_popfree_sound :
  popfree_spec SEGS (x_popfree A) ->
  forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (fun cs => summary_popfree A nx0 cs args).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanSoundSums ()) ["FPX_1"; "Sound"] "p'0p'1h04__x1h11Hh24__x2h32Hnh44__x3h54__x4h67__arithh74__p1h87__sat23h94__ffh:8__varmaph;5__with<7heq_cnth=5heq_eh>5Hcondh?4__x5h@5heq_DhA4__p2hB4__x6hC1rhD7__sat22hE1ni001nhF4__x7hG1zi011zhH3H22hI7__sat24hJ1bi021bhK1mhL3z22hM5Hlen0hN7__sat25hO4cstrhP4__p3hQ4__p4hR1ei031ehS1xi041xhT1li051lhU5FULL'hV2R'hW6model'hX1yhY2E'hZ3E10h[3E12h\3E14h]3E15h^2Hkh_3Hsdh`4__p5ha4__x8hb1ai061ahc1oi071ohd3HKche3Hpchf3H10hg3H12hh3H19hi3H21hj3Hehhk3Helhl3Hrrhm1ii081ihn3H23ho4Hsplhp7__sat26hq2e0i092e0hr5regs'hs3z23ht1Dhu3HKNhv2HRhw2Hahx2Hxhy3Whihz3Wsth{3X10h|2X2h}2X3h~2X4i0:2X5i0;2X6i0<2X7i0=2X8i0>2X9i0?5__x10i0@5__x11i0A5__x12i0B4__x9i0C2b1i0D2b2i0E2csi0F3cs'i0G2opi0H2sxi0I1Ei0J4FULLi0K3G10i0L3G12i0M3G14i0N3G15i0O5Gkeepi0P2HCi0Q3HC'i0R2HDi0S5HDdefi0T5Hbasei0U2Hci0V3Hc0i0W3Hcsi0X4Heh'i0Y4Hel'i0Z3Heri0[3Hfsi0\2Hii0]4Hleni0^4HloDi0_3Hmsi0`3Hnni0a2Hqi0b3Hr0i0c3Hrzi0d2Hsi0e1Ki0f1Mi0g2M'i0h1Ri0i3R10i0j3R11i0k3R12i0l3R19i0m3R21i0n3SUMi0o1Ti0p3Wloi0q1Xi0r2X0i0s2X1i0t2_Hi0u4argsi0v1ci0w3cnti0x2e1i0y2ehi0z2eli0{2ewi0|1ki0}2lbi0~2lki102loi115modeli121pi131qi141si151ti162k0i172l0p%0p%1p%2p%3p%4p&0p&1p&2p&3p&4p;1p;3p;2p;;p;4p;6p;5p;<p;:p;8p;=p;>p;Dp;7p;Bp-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8g002IR0p4p7210g0035R1p4p710R2p8p1003Sp4p710R3P2p8p106O3p6061000R4p102>7p4p7210R5p8P4g00c:R6p4p710R7p8P4P2p8P4P3p8P4p1003np4p7210R4p8p106PBp6061000R3p10269p4p710p8P3P7p8P3P2p8p107_Rp6061000R3P5p8P3g005aR5p4p710R8p8P3P7p8P3g018iR7p4p710p8P3p1047]p4p710p8P3p101>GR9p4p710p8P3P9p4p7210p8P3P2p8P3g01=AR9p4p710p8P3p1004fp4p73110R:p8P3p107]Wp4p7210p8P3p1005Bp4p710R3p8P4P2p8p1004Kp4p710P2p8P:P2p8P3P8p8P3P2p8g07j?k14>Tg07kAk34=Tg00G_S00k12HTg006=k10^Tg006bk10aTg007Gk12MTg007ek11;TP0k23QTg01RKR0k11}Tg04@5m;14Tg06V9S01k13@Tg07lFk42WTg01UJk30JTg04L:j1ZTg00>TS02j28Tg055Nk11=Tg050gj1mTg056Ak60mTg057>j5@Tg06X;m<3PTg04XDk62FTg05:Mj1DTg02cRk42eTg00eEk21KTg00@lj2yTg06[Jk12BTg00L5k11uTg00DOj1bTg04Cgj2HTg06BDj2CTg00O6k10<Tg02?1R2j24Tg03_cj1uTg0316k21PTg03BWk20pTg0339j2ATg01KQj21Tg04M6j2QTg03A6j5OTg06QSj5WTg00b8j1=Tg036>j2:Tg02^Jk20_Tg00G?k12kTg06[hk419Tg009Hj32k12XTg019]R3j2;Tg078Ok203Tg00ebk23OTg00gbk20BTg00>oR8j1MTg01kck20xTg01FXj27Tg013Mj3JTg03^=R:k23:Tg04Ekk12YTg03^]k437Tg01O`k30ETg00CYR4j2<Tg034[k23xTg00>8R;j25Tg036[k23tTg07mNk13rTg07nNk22NTg07nmk13qTg04VAk11@Tg07ook22oTg080Nk227Tg080mk23pTg081Lk23oTg082Mk13nTg082lk23mTg083ok13lTg084Qk63kTg085\k13jTg086\k43iTg087bk13hTg088ck43gTg089fk23fTg01K5k43eTP7k62nTg018QR7k20ATg027\k61jTg01n[k23bTg01kFk23aTg01oCk33`Tg00nSk13_Tg00I;k13^Tg00IYk13]Tg00Jgk22mTg00LWk23ZTg00M9k23YTg00Mek33XTg00NDk43WTg01:]k40HTg06^:m:24Tg00;0R<j1LTg00;Pj2?Tg06D9k83VTg035;k83UTg00cVj2aTg009bj2Bk13DTg03D2k83TTg01m@k13STg06b5m;3RTg03;Nk41[Tg02o9k223Tg02R_k22iTg00Dnk22hTg00EWk12GTg00F5k222Tg00JDk22gTg022;k33MTg07U8k31~Tg06_Mk53KTg07:Nk32cTg00:Lk33JTg00OTk20CTg08:kk22bTg00P4k32`Tg024dk63ITg08;Nk42_Tg02Zhk21zTg03a=k13HTg08;ok23GTg079Mk33FTg07;6k43ETP1j6Yk83}TP5k61wTg00`Jk31YTg020kk23CTg07cCk43BTg07cdk33ATg027>k12ATg029Ik13?Tg051bk50?Tg01lEk31_Tg052Tk31WTg00aFj2dTg01Z`S03k23>Tg08=0k22=Tg008Hj1VTg014Oj2KTg067<m=3<Tg00hAk23;Tg00`mj1sTg08>5k239Tg00dXk32ZTg08>Vk238Tg07`jk61mTg01b\k31rTg02Ohk20gTg08?9k236Tg016Qk41qTg01fNk435Tg07dEk333Tg07eMk20zTg00?lk232Tg00@Ok331Tg00Akk41MTP9k21pTg00BRk11STg02T]k20yTg02fZk31yk449Tg07h6k61|Tg02bRk21LTg01DZR9k22~Tg00D5k200Tg08?]m>2{Tg02eUk32TTg03:Jk22KTg0308k32lTg028Ek43\Tg00AFm<1\Tg08A4k64:Tg01GMk42yTg03K2k22xTg040kk648Tg06hfk647Tg01ogk645Tg06iNk343Tg06jOm:42Tg08BFk62wTg06;dmD3~Tg06mXm<3zTg059Pk11TTg00S@k31RTg03I5k31ATg053Pk41lTg054Nk22:Tg00KJk40TTg00TDk70ITg00Thk71BTg00Qkk30VTg02SHk32sTg00FVk32tTg00RTk228Tg02T1k22rTg00H?k23wTg00H]k40STg01Knk33vTg00S`k63|Tg02V7k33uTg00V0k80cTg01::k32qTg00?Ok241Tg00QFm<2vTg00C7k244Tg00ULk72OTg07bBk32QTP6k43sTg01=amB2pTg00^cR6f0R5g00_CR132p=>f2R=f1R>g04B3S0400x532p=eg05bO?2>5p>1]A26>5p=|%b5#bp>1Q203>5$2Yp>08g00W2R?/A5p=3f3R@1:=>'7/75p>0tg03>URA,:5p=F14>5,;=p=ff4RB/7@/7=/7>/75p=X17@=1A>5'7p>26%m>/;5p=`14>5#=p=N1:@A,7B/7=/7>/75p>0q11@=/4>,;B00g5#=p=vf6RC$1T$1@f5RD;JB?J@=?J>5p>0`1C=>0035p>1iPDPBP@P=P>%M5J1|p>25g03=QS0511=>,4@#=-2KB<1R5p=wQ05Q05@1A>581A=p>18Q04PDAJB@=P>%Z5H1l-2:C+0xp>0ZQ0400x5p=j%D>01P5p>0\g00VTRE?2>5p=0%D>00p5p>3NPDPBP@%m=P>P5J0mp=EPBP@P=g00lgS06P>P5J1wp=r&1TB$1@?J@=?J>5p>3LAJB@=?J>5p>1dQ05@1A>5p>1{PBP@Q05@1A=>P5H1lp>2aQ0422:>5+0xp>2DQ05P@P=P>P5H1981ABp>05Q05PCPDPBP@P=%M>J1|<1A5p=}1H=>=2@5p=n%D=1C>5+0pp>0i&1T=$1@?J>5p>2CQ05PCPDPBP@P=P>J1|<1A5p>0XQ04PDAJB@=P>P5H1l-2:C+0xp>121:B@,7D/7=/7>/75p>1U17B@1:=A'7/7>/75p>02%==9JB@?J>5p>101A?>/75p>1H17=>/75p>1s11=>/45p=q20g>5#=p>2]14=>,;@00g5#=p>2\&1T5$1@p>0w%=59J=>p>3=%u5-03>p>2<Q0520_DB11=>,4@#=+2K<1R5p>011:>5,7=p>1V1A>5,7=p>2[1C=>%u5+03p>1Z1:>A,7=/75p>3014=>/A5p=I1:B@,7D/7=1:>A'7/75p>1514>5,;=/:Ap=p17DB/7@/7=1A>5'7p>2;%m>/;5/:Ap>0417DB1Q@='7/7>/75p>2I1:@=,7B/7>/75p>1h17B@/7=1:>A'7/75p>2zA26>1A2651'8p>0>1;>5/:Ap>1>f7RF/7C/7D/7B/7@/7=/7>/75=261p>0b11>5,4=#=p>2u17@=/7>/75=261p>1C1A=>,7@/75p>3{14@=/A>,7B/75p>3y17>5=261p>291<?5p=9155Ap>2P11=>/45,;@p=z&1TC$1@?JDB14>5,;=#=7J@p>3d1C@=14>5#u+03p>0s20g@=#=9JDB?J>5p>1?Q05%D@P=P>P5H1981ABp>0rP@P=P>P5H1l-2:Bp>0R&1TC$1@%=B7JD14>5,;=#=7J@p>1<1;B@P=P>P5H1lp>3c15?5p=o1yE5p=6g00WPRGPEP7P<P;g01>dRHg00]]RIP?P@P=P>P5N<1\p>1kPGPEP7P<P;PHPDPBP@P=P>P5N<1\p>1^22mE5p>0oPEP>g00_cRHP5H0Tp>0nPDg00Z4R;g00ZSR7P7g00[3RJPBP;P7P7PJP@g00\:RKK0IP=P;P7P7PJPEP>PHP5H0TPKK0IK1Bp>1g1<?>155A'8p>1:1d@==2B>/85p=R1d=>=2@5p=g1d@=1a>552Bp>0G1<?>/85p>0N%=5-23>p>1720_>5-1L=p=]1;=>/<5p=_18>5,8=p>1f22hE5p=kB0VE>5p=SB2sE=>>0VE5p>1eB0VE>5:0VE=p=^B2tE=>>0VE5p>0]g00YHS07B0VE=>g00X\RL+28-2r@<1R5p>16Q07228>L<1R5p=[23wE5p>0FPEP=P>P5H0Sp=xPEPEPCPDPBH0SP@PEP=P>P5H0SH0Sp>2122gE5p=lB3vE>5p=tP=P;P7P7PJPEP>g00[SRMP5H0TPKK0Ip=cP=P;P7P7PJPEP>g00^<RNP5H0TPKK0Ip=UP>P;P7P7PJP5J3|p={P=P;P7P7PJP>P5K1Bp=\B3uE>5p=iP=P;P7P7PJPEP>PHP5H0TPKK0Ip=hPDP;P7P7PJPBP@P=P;P7P7PJP>P5K1BL0cp>2fPDP;P7P7PJPBP;P7P7PJPEP@PNP=H0TPKK0IP>P5L0cp>06PDP;P7P7PJPBP;P7P7PJPEP@PHP=H0TPKK0IP>P5L0cp>13PCP;P7P7PJPDPBP@P;P7P7PJP=P>P5L0cL0cp=GPEPBP@P=P>P5J1wp>0j1B=>/;5p>1J1?>592@=p>1IB2qE>5p=~B2sE>5p>0UPBP;P7P7PJP@P;P7P7PJPEP=PNP>H0TPKK0IP5K1Bp>0hPDP;P7P7PJPBP;P7P7PJP@P=K1BP>P5L0cp>0KPEPBP@P=P>P5EYp>0uA2E5?p>1c14>5,1=p>0OPEPEPBP@P=H0SP>P5H0Sp>0915>5,8=p>1F11>5,?=p>1x14>5,1=,?@p>071?>5,B=p>0@PDP;P7P7PJPBP;P7P7PJPEP@PMP=H0TPKK0IP>P5L0cp>0:11>592E=p>0;PEPEPEPCPDPBH0SP@P=H0SP>P5H0Sp>0eP@P;P7P7PJP=P>P5L0cp>1v11>5,4=p>0~241?5p=PPEPGPEPEP8PBP<P@g00WoP=P>1yE5N<2vp>0MPGPEPEPEP<P<PDPBP@P=P>P5N<2vp>1tPEPEP4PFP4PCPDPBP@P=P>P5N<1\p>1n244?5p>0P15?BA2E@='81<>?A2E5?'8+00p>0YB2tE>5p>0QPEP>PMP5H0Tp>1XP@P;P7P7PJP=P>P;P7P7PJP5PKK0IK1Bp>0|PDP;P7P7PJPBP;P7P7PJP@P=K2OP>P5L0cp>0DA2E=>,8@0005p>111<5?p>0{1;>5,?=p>1b%M5:2Q=>p>0v14>5,;=,?@p>0l11@=/4>,;B00g5,?Dp>0}A2=>5#sp>1D1d>592@=p>2@A2@=>/85p>2?A2CDBA2@=>/85'8p>2J1d@=1d>552Bp>0d11=>/15p>1G14=>,;@00g5,?Bp>2>14>5,;=#=p>1`g00keRMP=P>P5H3sp>0L1a>592@=p>1ag00jDS089265p>0=A2G>5p=T1;=>00g5p>1EB2Q=>5-1p@p>34%M5:2Q=>-1p@p>0WPGPGPGPEPEPEg07i<P<P<P<P2g07i\PDPBP@P=P>P5NB2pp>0kPGPEP5P<P>P=P@PBPDPCPFf8R2N<1\p>1OB0VE>5028Lp>0fQ07Q07@1R>581R=p>0[P@P;P7P7PJP=P;P7P7PJP>PKK0IP5K1Bp>2VPEB2qE=>PNP5H0Tp>2^PBP;P7P7PJP@P;P7P7PJP=PKK0IP>P5L0cp>2d18=>0005p>1oPGPEP9P<P4g01GhPDPBP@P=P>P5N<1\p>2}Q07@1R>5p>2EPEPBP@PEP=P>P5H0SH0Sp>2015?>/85p>2|A2E5?,8>p>2UB0VE>5:0VE=:0VE@:0VEBp>1NAJCDB1C=>00357J@p>2j%D@P=P>P5H19p>2S2285L-2r>p>2L1<>?/85p>3[PEPEPEPEPEPEP3P5P>P=P3P@PBPDPCPFP2f9R3NB2pp>2RPBP;P7P7PJP@P;P7P7PJP=P>K1BP5K2Op>4<18>5-00=p>4;P=P;P7P7PJP>P5K2Op>46&1TB$1@%==7J@?J>5p>40p,2fxRLp,4SEGSR4p,1AR<$4>S0944=&2HMS0:Q04Q04g00jdS0;g00\ZS0<$0^S0=$0aS0>$2MR9Q0=$0^S0?$0^S0@$0^S0A$0^RK$0^S0B$2MRN$1;R8+3QS0CQ0@$2M$1;S0D$1}S0E\8S0Fg04C1S0Gg05ffP4P<p,5LIMITS0Hp,4SINVS0Ip,4argHS0Jp,3FS0S0KPBPCP@P=P>N;14S0L&3@F#>Q04$1}RHP<p,3nx0ROP2P3H2W;eFQ0;Q0CQ0FQ0Gf;RP>0JO@f=RQ#Z@0JP@'8P4P<Q0HQ0IQ0JQ0KPBPQP@P=P>N;14&1==S0Mf:RR$1=+1]p,3bmKRSP4p,4scfgRTPLP4PDf?S0N#mRUPBP@J0mPRD@[[[]W]U]V]YP@P4P<Q0HQ0IQ0JQ0KP2PRPFPCPDN;14P4P<Q0HQ0IQ0JQ0KP3PPP2PFPCP5N<3PP4P3P<Q0JP3PPPCPFJ2F%DPH2eP<Q0JPRf<RVPFP2J2FQ0F%mQQ09+1KP61y65S0Of>RW#mQ09+1K/|5P6f@RX#mQ09+1K/|5P6PH&2B>Q04$1uRYQ00PMPHfBRZPYPMPHP>Q00PMPHP>P0PEPHfDS0P%bIS0Q#bS0R#bS0S#bS0T#bS0U#bS0V#bS0W#bS0X#bS0Y#bR['HP0PEPHfES0Z%b[R\#bR]'HP0PEPHfFR^%b]S0[#bR_#bR`#bS0\#bS0]$1QS0^$1QS0_'HP0PEPHfGRaQ0^'HP:PMPEPHfHRb/C\Q0?$0<Rc/45S0`#uRd+08P0PEPHfJS0a#DReQ0a/C\Rf+1PP0PEPHfKRg#DRh1Cg\Ri+0pP6PH%3FS0bPFPB14cBS0c/A>RjH0t%F5Rk%3CRl%3DRm11BFRn=fCDRo#FDXRp%32S0dP2PnH26RqfLS0e&0<KRK'`RrQ0e,QOQ0e#DRsPsP@P=1NcnRtDOP<PsP@P=PtDWI0qQ0ePrQ0eP[%=BRrP]%=oRoP_PCPnQ0<$0<RuPDQ0A$0<RvDvRwK0`P`Q0eQ0c#uRx81i\P@P=PnPCPDP2J25RyP6Q05$2HS0f1:2n20_@=RzPcPnP2Q05$2kR{DwP{n0100000020000R|PsP@P=PtH19418Q0eK0ZPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800PYn10110500020120109117PYPYPYPYPYPYPYn0110300081110e101003010G1061023010G1061023010G1061023010G1061024010H1101001094010H116108100n10110u00020021103105S0gn0100000020001%jXS0h52HPSP4PTPLP4Q0N%mZRsPWPQJ0mPVD@S0i]3]eP>Q09-1KUS0j#>P6PH&2B1PYQ00PMPHfARUPYPMPHP>Q00PMPHP>P0PEPHfCR}/H[P0PEPHQ0P/H]P0PEPHQ0ZQ0_'HP0PEPHQ0^,H^P:PMPEPH1Ca\008dP0PEPHfIR~1C~\+0\P0PEPH20pefP6PHPq%mgS0k/;KRf1QOgPhPhP@P=PtDOP<PhP@P=PtDWI0qPgPfPgP[PrP]PoP_PwK0`P`203ixPhP@P=PtH19:18y|PgK0ZPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800PYn10110500020120109117PYPYPYPYPYPYPYn0110300081110e101003010G1061023010G1061023010G1061023010G1061024010H1101001094010H116108100n10110u00020021103105S0ln0100000020001Q0N#jS0m52HQ0221K>5S0n#>10=>S0o[Rh10>5S0p21K=>S0q#>Rf[10@=\f23O>5P>n2001000000120000000XKEXEEPh^KE^EEP5PsQ09P=O3Q09,0sQ00PMQ00PMPHP5PYPMPHP>Q00PMPHP>P0PEPH1Ha[P0PEPH1Hb]P0PEPHQ0_,H~P0PEPHQ0aQ0^'HP:PMPEPH208idP0PEPHfMRi1Ci\S0r+0\P0PEPHfNS0sQ0s/C\S0t+3NP6PHPqfOS0u#mS0v/;KRsQ0u,QOQ0u#DRhPhP@P=PtDOP<PhP@P=PtDWI0qQ0uPsQ0uP[PrP]PoP_PwK0`P`Q0u/C\Rs003xPhP@P=PtH19:18y|Q0uK0ZPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800PYn10110500020120109117PYPYPYPYPYPYPYn0110300081110e101003010G1061023010G1061023010G1061023010G1061024010H1101001094010H116108100n10110u00020021103105%j}S0w52HPSP4PTPLP4PZQ0ZPUPXEEQ0ND@Rf]3Q0PAeHYZPHPYP0Q04p-0ReP5g00mCS0xg00m`S0yn10110700021000000S0zXRHS0{Q0wP5DrQ0x20Bf5b1W3PMQ0:PMPHP>Q00PMPHP>P0PEPH1H~[S0wP0PEPHQ0a/H]S0|P0PEPHQ0_,HgS0}P0PEPHQ0eQ0^'HS0~P:PMPEPHQ0r008dS0rP0PEPH21PhsS10P0PEPHfPS11#DS12Q11/C\Rs+0pS13P6PHPqfQRq#mS14/;KS15#FS161QOqS17%DqRhPhP@P=PtDOS18P<PhP@P=PtDWS19DXQ15PqP[PrP]PoI3LP_PwP`1Cq\Rf003xI1dS1:PyPhP@P=PtH19Ry-1{|%ZqS1;I2a-2DqPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800PYn10110500020120109117PYPYPYPYPYPYPYn0110300081110e101003010G1061023010G1061023010G1061023010G1061024010H1101001094010H116108100=eHaPSP4PTPLP4P^P~Q0ZQ0PEEP}D@]3]TP5Q0:Q00PMQ00PMPHP5P0PEPHQ0a/H[R|P0PEPH1Hg]P0PEPHQ0eQ0_'HP0PEPHQ0^,HiP:PMPEPHQ0t008dP0PEPHQ1201PsP0PEPH20phfP6PHPp%3RPRPnH26fRRf/`KRh1QOf%DfRsPsP@P=PtDOP<PsP@P=PtDWI0qPfPhPfP[PrP]PoP_PwK0`P`1Cf\Rh003xP@P=PnPCPDPRP6Q0f1:RnPzPcPnPRP{DwP{n0100000020000PsP@P=PtI05F}PfK0ZPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800PYn10110500020120109117%j~S1252HPSP4PTPLP4PbQ0kPaP^J0mQ0ZD@S0k]3P5P0PEPHQ0wP0PEPHQ0|P0PEPHQ0}P0PEPHQ0~P:PMPEPHQ0rP0PEPHQ10P0PEPHQ13P6PHPp%33P3PnH26Q16Q17Q18Q19DXQ15Q1:P@P=PnPCPDP3J25P6Q0f1:3nPzPcPnP3P{DwP{n010000002000001{yQ1;I2a-2DqPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800%jbS1;52HP|&1}ER|1y|5S1:P|PgP[P5CnP0PEP|PiP[P5CnP0PEPHP>P0PEPHQ0u/H]S15P0PEPHQ11Q0_'HS19P0PEPHQ0^,HqS18P:PMPEPH208hdS17P0PEPHfTS16Q16/C\+0\S13P0PEPHfUS10Q10<0i\RhP6PHPp%3WS0rPWPnH26fVS0~/`KRp#FS0}Q0~,QORyQ0~#DRsPsP@P=PtDOP<PsP@P=PtDWDXQ0~PpQ0~@2C[rS0|P]PoP_PwI1dP`Q0~@1i\xS0wP@P=PnPCPD%MWRwP6Q0f1:WnPzPcPnPWP{DwP{n0100000020000PsP@P=PtI05K0XQ0~#ZRtK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00PYn10110400021110800%jiS0t52HPSP4PTPLP4Q0eQ0vPgQ0aJ0mP~D@S0v]3]fP>P|Q0sP[20xE5RnCnP0PEPHQ15P0PEPHQ19P0PEPHQ18P:PMPEPHQ17P0PEPHQ13P0PEPHPhP6PHQ0dP2PBPjPkPlJ1UPm11B2Rh=fCDRoQ0r1AWhI02Q0}PyPsPsP@P=1NchRyDOP<PsP@P=PyDWDXQ0~PpQ0|P]PoP_PCPhPuPDPvDvI10P`Q0wP@P=PhPCPDPwP6Q0f1:WhPzPcPhPWP{DwP{n0100000020000PsP@P=PyI05K0XPtK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00Q0s#jS0w52HQ11/H]P|Q1:P|PqP]P5CnP0PEP|fSS0|P]P5CnP0PEPHP>P0PEPHQ10Q0_'HS0}P0PEPHQ0~Q0^'HS0rP:PMPEPHfWS0d/C\008dS13P0PEPHfYS17Q17/C\+0\S18P0PEPHfZS19Q19<0i\S15P6PH1:QB-1HQ@1sjkS1</7lPm11BQRt/4DRy,;CRs%3}S1=1A}tS1>I02f[Rh#mS1?/;KRw#FS1@1QOhS1A%DhRoPoP@P=1NctRpDOS1BP<PoP@P=PpDWS1CDXPhPwB2Ch[rS1DP]PsP_AqtuDRs,;C02]vI10P`B1ih\xS1EP@P=PtPCPD%M}S1FP6Q0f1:}tPzPcPtP}P{DwP{n0100000020000PoP@P=PpI05RpK0X%ZhRoK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400PYn10110400021110v00Q0|#jS1G52HPSP4PTPLP4PfQ10PqQ11EEQ0uD@S1H]3]gP>P|Q16P]PnCnP0PEPHQ0}P0PEPHQ0rP:PMPEPHQ13P0PEPHQ18P0PEPHQ15P6PHQ1<Q0b'7Pm1;FyRyQ1=Q1>I02Q1@Q1AQ1BQ1CDXPhPwQ1DP]PyP_1;Fs02]vI10P`Q1EP@P=PtPFPDQ1FPpK0XPoK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400Q165eHQ0~Q0_'HP|Q1:P|Q0dQ0_P5CnP0PEP|Q17Q0_P5CnP0PEPHP>P0PEPHQ0^,HhS1FP:PMPEPHf\S1E/C\008dS1DP0PEPHf^Ro1Co\+0\S1CP0PEPHf_Rp@0ip\S1BP6PH%3ZPZPBPjPk%3VJ1US1APm11BZRm=fVDS1@%3bS1>1AbmS1=I02f`Rt/`KRs#FS1<1QOtS0b%DtRyPyP@P=1NcmRwDOS15P<PyP@P=PwDWS18DXPtPsB2Ct[rS13P]Q1@P_PV11muS1@PDPvH2\I10P`B1it\xS0rP@P=PmPVPD%MbS0}P6Q0f1:bmPzPcPmPbP{DwP{n0100000020000PyP@P=PwI05RwK0X%ZtRyK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000PYn10110400021111400Q17#jS1I52HPSP4PTPLP4fXS1JQ1?Q0dQ0~J0mQ10D@S1?]3]iP>P|Q19Q0_PnCnP0PEPHQ1FP:PMPEPHQ1DP0PEPHQ1CP0PEPHQ1BP6PHQ1APlAfVmCRlQ1>Q1=I02Q1<Q0bQ15Q18DXPtPsQ13P]PlP_PVQ1@PCPvH2\I10P`Q0rP@P=PmPVPCQ0}PwK0XPyK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000Q195eHQ1EQ0^'HP|Q1:P|f]RyQ0^P5CnP0PEP|PpQ0^P5CnP0PEPHP>P:PMPEPHfaRw/C\S0}008dP0PEPHfcS0rQ0r/C\S1@+0\S13P0PEPHfdRd@0id\S18P6PH%3aS15PaPBPjPk%3US0bJ1U%3PS1<11BaRj=fUPS1=%3iS1>1AijI02feRm/`KS1A#FS1B1QOmS1C%DmRlPlP@P=1NcjRsDOP<PlP@P=PsDWDXPmQ1A&0wmS1D?J[rP]Q1=P_PUPjPuPPPvDvI10P`1Cm\Rr003xP@P=PjPUPP%MiS1=P6Q0f1:ijPzPcPjPiP{DwP{n0100000020000PlP@P=PsI05K0X%ZmS1FK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~PYn10110400021110000%jpS1K52HPSP4PTPLP4PoPwPyQ1EEEPhD@S1L]3]hP>P|PtQ0^PnCnP:PMPEPHQ0}14c>S1M#uS1N+08P0PEPHQ13P0PEPHQ18P6PHQ15PaPD14cDS18/A>PkQ0bJ1UQ1<11DaRs=fUPRjQ1>1AisI02Q1BQ1CPlPlP@P=1NcsRxDOP<PlP@P=PxDWDXPmQ1AQ1D@3=[DP]PjP_PUPsPuPPPvDvI10P`Q18#uS1D-03rRrP@P=PsPUPPQ1=P6Q0f1:isPzPcPsPiP{DwP{n0100000020000PlP@P=PxI05K0XQ1FK12PYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~=eHtfbS1F/C\14c=S1=#u+0823:MERx1yx5Q1@14c@S1A#u+08=2x5P:PMPE&2Yr=2x5P:PMPEPHP>P0PEPHfhS1@Q1@/C\S1C+0\P0PEPHfiR:#DS1B1C:\S1<+0pP6PHQ0e#3RrQ0ePR14cRS13/A>Pk%3^S0}J1U%3XQ0e,1RRl=f^XS1O%3fS1P1AflI02fjRs/`KS1Q1QOs%DsRjPjP@P=1NclS1RDOP<PjP@P=Q1RDWI0qPsQ1QPsP[%=RP]Q1O#=P_P^PlPuPXPvDvK0`P`1Cs\S1OQ13+2<P@P=PlP^PXPfP6Q0f1:flPzPcPlPfP{DwP{n0100000020000PjP@P=Q1RI05F}PsK0ZPYn0100000020100PYn10110400021110y00PYn10110400021110z00n200110400012110}10~=eHmPSP4PTPLP4PdfgS1RQ0rQ1FEEPwD@]3]oP>Q1C14c2S1Q#u+08PMPEP>P5H3752xP0PEPHQ1BQ1<+1PP0PEPHQ1O-0pjP6PHQ1>PiPP14cPS1</A>PkQ15J1UQ0b11PiRx=faURlQ0|#3S0bQ0|/AxI02fkS15/`KS1BQ15,QOQ15#DRzPzPBP@1NcxS1CDOP<PzPBP@Q1CDWI0qQ15Q1BQ15P[%=PP]%=lP_PaPxPuPUPvDvK0`P`Q15/C\RlQ1<+2<PBP@PxPaPUQ0|P6Q0fQ0|/:xPBP@PcPxQ0|P{J01P{n0100000020000PzPBP@Q1CI05F}Q15K0ZPYn0100000020100PYn10110400021110y00PYn10110400021110z00Q1@5eHQ1O-1PjP|Q1:21Pzl=2|5P0PEfmS1OQ1O/C\+0\=2|5P0PEPHP>P0PEPHfoS1CQ1C<0i\S1BP6PHQ1P@1VfXS1S14cXRl<2[>@1skrQ0}Q0e11XfRz;f^Rj#FS1TQ1J#3S1UQ1J/AzS1VDXfpS1W/`KS1X#FS1YQ1W,QOS1ZQ1W#DRxPxP3P21NczS1[DOS1\P<PxP3P2Q1[DWS1]DXQ1WQ1XQ1WP[%=XP]%=jP_Q0ePzPuP^PvDvK0`P`Q1W/C\Rj02<lP3P2PzQ0eP^Q1JP6Q0fQ1J/:zP3P2PcPzQ1JP{J01P{n0100000020000PxP3P2Q1[I05F}Q1WK0ZRzPYn0100000020100PYn10110400021110y00PYn10110400021110z00Q1O#jS1[52HPSP4PTPLP4flS1XQ1CQ15PsEEP:D@S1^]3]kP>fnS1_Q1_/C\+0\=2|nP0PEPHQ1BP6PHQ1S@2[l=@1skrQ0}Q1TQ1UQ1VDXQ1YQ1ZQ1\Q1]DXPzPYn0100000020100PYn10110400021110y00Q1_5eH20pxjP|Q1:fqS1:Q1:<0i\=2|5P0PEfsS1]Q1]<0i\=2|5P0PEPHP>P6PHQ0d#3S1\Q0dQ0ZQ0Z,4cS1Z/AFH0tRj%3qS1Y81sk%3gS1VQ0ZQ0d'1Rk=fqgRx#FS1T%3yS0}1AykS1SDXfuS1B#mS1`/;KS1a#FS1bQ1B,QOS1cQ1B#DRzPzPWPQ1NckRlDOS1dP<PzPWPQPlDWS1eDXQ1BQ1aQ1BP[Q0Z#=P]%=xP_PqPkPuPgPvDvK0`P`Q1BQ1Z81Z\PWPQPkPqPg%MyS1aP6Q0f1:ykPWPQPcPkPyP{J01P{n0100000020000PzPWPQPlI05K0XQ1BK0ZRlPYn0100000020100PYn10110400021110y00Q1]#jS1f52HPSP4PTPLP4frS1gQ1`Q1:Q1WJ0mQ1CD@S1`]3]jP>ftRz@0iz\=2|nP6PHQ1Y:30j>Q1VQ1TQ0}Q1SDXQ1bQ1cQ1dQ1eDXPlPYn0100000020100=eHzQ1UQ1JP^AIc^2P=Q1PJ15PrQ1J,1^RrQ0e5pf%3oS1PPoPrJ2;fvS1e004KPOQ1eQ1e#DRlPlQ0NPW1NcrRrDOP<PlQ0NPWPrDWJ2IP6Q0OQ17#3S1dQ17PaAIca3P@Q0bJ15Q1>Q0|Q17,1aRr;pi%3pS1>PpPrJ2;fwRl004KPOPl%DlRjPjPXQ0N1NcrRrDOP<PjPXQ0NPrDWJ2I/|5P6%3hS1cPhP~14c~S1b/APPDQ10#3S1SJ15Q0u#3Q1011~hRrQ0u3fS1T%3wS1V1AwrI02fyS1h/`KS1iQ1h,QOQ1h#DS1jQ1jPZPU1NcrS1kDOP<Q1jPZPUQ1kDWI0q/|5P6PHP>fzRj1`jKS1lPjP[Q0a#=P]Q0~Q0aQ1E'1RnQ113fS1m#=P_Q0~PnPuQ11PvDvK0`P`Q0a,4cS1n:1Zj\P}PZPnQ0~Q11Q1FP6Q0fQ1F/:nP}PZPcPnQ1FP{J01P{n0100000020000%DjRkP}PZ1NcnS1oI05F}PjK0ZPYn0100000020100Q1h#jS1p52HPSP4PTPLP4fxS1qf{S1r#mS1sPlQ1eJ0mQ1BD@S1t]3]>P>Q19#3S1uQ19PbAIcbRPBQ16#3J15Q0s#3Q16Q19,1bRxQ0s3p%3tS1vPtPxJ2;Q1q004KPOQ1qQ1q#DS1wQ1wPUPX1NcxRxDOP<Q1wPUPXPxDWJ2IS1w#>Q1hQ1iQ1hP[%=~P]Q1T#=P_Q10PrPuQ0uPvDvK0`P`Q1hQ1b81Z\PZPUPrQ10Q0u%MwS1bP6Q0f1:wrPZPUPcPrPwP{J01P{n0100000020000Q1jPZPUQ1kI05K0XQ1hK0ZQ1q#jS1k52HQ1E#3S1jQ1EQ0aQ1n/AV%FCI1hQ0~#3S1nQ11#3Q1mQ1F#3S1mI2zQ1F/AnQ1l1QOjPkPkP}PZQ1oDOI02RnP<PkP}PZQ1oDWRk<0E>20>nkQ02Q0}PyPgAIcgQPFQ1\J15Q1YQ0d11gyRk;pqQ0r#3S1YQ0r/AkQ1s01>KQ1r,QOQ1r#DRnPnQ0PP}1NckRkDOL0bP<PnQ0PP}PkDW#>PSP4PTPLP4Q1hf|S1sQ1qPlEEQ1eD@P5Q1>PpPiQ0N9IciP3Q1dJ15Q0bQ1711ipRkQ0|3p%3mS0b1Amkf}Rn004K1QOn%DnRrPrP^Q0Z1NckDOL0bP<f~S1d#DPaP^Q0s>2uctDW#>Q1VPwQ0uQ0u=IcUH0tPPQ1cQ1SQ0u/1wRkQ105phI0qQ1R#3S1SQ1R/Akp+01@S1\004KQ1\,QODXRrQ1\#DRxPxPbPa1NckDORk<0E>20>rkQ02Q1mQ1FQ11Q11=IcZ%FVI1hQ1jQ1nQ1EQ11Q1F'1RkQ0~3pQ1@#3S1nQ1@/Akp+01ARr004K1QOrL0b%DrRxPxP~Pb1NckDO#>PSP4PTPLP4Q1dp+01BS1jPnQ1sEEQ1rD@P5%3dS1oPdPfQ0P9Icf%FWI1hQ1PQ1U11fdRkQ1J5po%3sS1U1Askp+01CS1P004KQ1P,QOL0bp+01DS1l#DRkPkQ0ePgQ0|>2ucmDO#>ffRk#3S1TQ1681VkQ16=Ic^PXQ1vQ1uI02Q16/1kRxQ195ptQ1X#3S1uQ1X/Axp+01ES1i004KDXS1xQ1i,QORx<0E>Q1x00>xQ02Q1SQ1RQ10Q10=IcaH0t%FUQ1VQ1cQ10Q1R'1Rx=pwhQ1O#3S1cQ1O/Axp+01FS1V004KL0bQ1V,QO#>PSP4PTPLP4Q1lp+01GS1xQ1PQ1jEEPrD@P5%3:S1yP:Q0dQ0d=Ic~H0t%F}Q1YQ0}Q0rQ0d/1:Rx;pyQ1C#3S0}Q1C/Axp+01HS1Y004KL0bp+01IS1z,QO#>Q15#3S1{Q15Q17Q17,4cS1|/AgQ0ZQ0bJ15Q1>Q17Q15'1Rx=pmpQ1:#3S1>Q1:PxJ2;S1}p+01JS1~004KRx<0E>Q1}00>xQ02Q1uQ1XQ1941VQ19Q0e5Ic%F^Q1TQ1vQ19Q1X'1Rx=pktQ1g#3S1vQ1g/AxL0bp+01KS1T004K#>PSP4PTPLP4Q1zp+01LS1}Q1YQ1xEEQ1VD@P5Q1_#3S20Q1_Q1E41VQ1E,4cS21Q0s'A%FbQ1nQ1mQ1@Q1EQ1_'1RxQ1F3p%3zS1m1AzxL0bp+01NS1n004K#>Q1W#3S22Q1WPoQ119IcoQ0a#FI1hQ1UQ1oQ1W,1oRx=psdQ1e#3S1oDXS23Q1e/AxRx<0E>Q2300>xQ02Q1>Q1:/:pAIcpq%FgQ1{Q0bQ15Q1:,1pRx;pm%3lS0bL0b1Alx#>PSP4PTPLP4Q1np+01QS1np+01MS1{Q1}EEQ1TD@P5Q1]#3RxQ1]/:wQ0|9Icw%FiQ1cQ1SQ1OQ1]Q1R5qw+1>Q1h#3S1SL0bQ1F/1z,Aj#>Q1B#3S1cQ1BQ0rQ0r,4cS1}Q10'AH0tQ0uQ0}Q1yQ1CQ0rQ1B;q:+1>I0qS1yQ1r#3S23<0E>Q1yQ23+0>Q02Q1oQ1ePd14cdS1oQ0~'AQ11#FI1hQ22Q1UQ1WQ1e=qds+1>H1CQ1s#3S1U#>PSP4PTPLP4p+01SS22p+01VS1yp+01RS24Q1nEEp+01PS1nD@P5Q1qQ1q/:k+1H14ckS25Q1J%FfH3{Q1vQ1uQ1gQ1qQ1X5qk+1>H1CQ1\#3S1u#>S1v%3jS26Q1@81VjQ1@Q195IcQ16Q1mQ20I02S20Q1@Q1_7qj-1>zRz<0E>Q2000>zQ02Q23Q1rP:AIc:hH0tQ10#FQ1cQ0}H1CQ1BQ1rQ1C5q:+1>#>PSP4PTPLP4p+01XS0}p+01[Rzp+01WS1cQ1yEEp+01US23D@P5%3nPnQ15Q15=IcyH0tQ0d#FQ0bQ1>H1CQ1qQ1XQ1dQ1g3q+1>#>Q1uQ1\Q1OQ1O=IcpQ17Q1SJ15S1S@0Ex>Q1S00>xQ02Q1_,:r-1HrQ1_=IctQ19#FQ26H1CQ1m#>PSP4PTPLP4p+01]S1mp+01`S26p+01\RxPzEEp+01ZS1SD@P5Q1P#3S1uQ1PQ1W41VQ1WQ1F5IcQ1E#FQ1UH1CQ0b#>Q1iQ1iQ1g':+1HPcQ1gPd%FoI3yS0bQ1d#3S1U<0E>Q0bQ1U+0>Q02Q1V#3Q1VQ1]':Q1]=Icm%FpH1CQ1vPSP4PTPLP4p+01bS1vp+01eS1Up+01aS0bQ26EEp+01_S1>D@P5Q1Y#3Q1YQ1B':Q1BQ1R5Ic%FwH1CQ1u#>Q1~#3Q1~PlAIcl:H0tS1uQ0r#FRl<0E>Q1u00>lQ02Q1TQ1TQ1q':+1HQ1q=Ics+29%Fd#>PSP4PTPLP4p+01gRlp+01jS1up+01fQ1UEEp+01dS20D@P5Q1{Q1{/:j+1HQ1X9Icj+29Q1R#F#>p+01OS27Q27Q1s':+1HS28Q1sQ1_5IcRj<0E>Q2800>jQ02Q1n#3Q1n/:n+29Q1C9Icn#>PSP4PTPLP4p+01lS28p+01oS29p+01kQ1uEEp+01iS2:D@P5Q24#3Q24Q1\':+29Q1g9Icr#>p+01TRn#3S2;Q1j,:nRj<0E>Q2;00>jQ02Q23#3#>Q23Q1P':#>PSP4PTPLP4p+021S2;p+024S2<p+020S2=Q29EEp+01nRjD@P5Q1c#3#>Q0}Q1V':#>Q021A>5#>1<=>[S0}1<>5S2>1A=>#>S2?[Q2?1<@=[23x>5P>n2001000000120000000XKEXEES2?Q0}^KE^EES0}P5P?Q1SP=O3Q1S#9Q2?Q0}P5Q1vQ1~/1xS1~Q0~O3Q1vQ1~'<Q2?Q0}P5P?Q20Q0|O3Q20#9Q2?Q0}P5P?PnPgO3%9nQ2?Q0}P5P?PxPbO3%9xQ2?Q0}P5Q24,4cS24Q1lPXO3Q24Q1l'<Q021:>5#>15=>[S2415>51:=>#>S0}[Q0}15@=[23t>5P>n2001000000120000000XKEXEES0}Q24^KE^EES24P5p+02DS2?/`KS1~PAPmO3Q1~$2PQ0}Q24P5Q1vQ1yp+01hS1~PxCzS2@PAQ1JO3Q2@$2PQ0}Q24P5Q1lPAPgO3Q1l$2PQ0}Q24P5Q28Q1SP}O3Q28Q1S'5g08CPS2@$1}S2AQ04Q2AP0Q2@Q04P5P5p+02KS2Bn10110700021000000Y15Q2@p+02JS2C+0xS2DQ2@Q2BQ2B$3r02NKQ2B$3q$1@P[%=zS2EP]p+01mS2F-2ozS2GQ0b+27-2Nl#=I1dP_Q2G02ouQ0b+27-2Nl03pvP`Q2B03o\227cz$3n+3mI10PnQ22Q2GPlQ0bp+023S2H$3lJ3kP6Q0fQ2HQ2F,1zR0':PnQ22PcP0Q2HP{J01P{n0100000020000S2IQ2B$3jPnQ22Q2G-27c#=H3i418Q2B$3hH3g+3f+0xS2@Q2AQ2@Q2DPrH3eJ2nQ04Q2CQ2BQ2B/`KQ2BP[Q2EP]PlP0Q0bK3dP_PlP0PuQ0bCzPvP`Q2BP\PcPzH0sJ1?PnQ22P0PlQ0bQ2HQ2IQ2BPnQ221Nc0I0rF}Q2B#ZI0R32Q04p+02LS2IQ2I/`KQ2IP[PxP]Q1~11xjR0Q1vK1<P_Q1~P0PuQ1vCzPvP`Q2IP\PcPxH0sJ1?Q23PnP0Q1~Q1vQ2<P6Q0fQ2</:0Q23PnPcP0Q2<P{J01P{n0100000020000Q2IQ23Pn1Nc0I0rF}Q2I#ZI0RR0Q04p+02MS0bQ0b#mPKQ0bP[Q1mP]Q2:Q1mQ29'1Rnp+01cRlK1<P_Q2:PnPuPlCzPvP`Q0bP\PcQ1mH0sJ1?Q1yQ23PnQ2:Plp+025S2:P6Q0fQ2:/:nQ1yQ23PcPnQ2:P{J01P{n0100000020000Q0bQ1yQ231NcnI0rF}Q0b#ZI3c+2D=eH5Q0;Q0CQ0FQ0Gp+02PS1y>0JO@p+02RS2E#ZRnQ1y<0J@'8Q0LQ0Mp+02OS2D$1=+1]PSP4PTPLP4PDP2PBP@EEQ2DD@[[[]W]U]V]YPSP4PTPLP4Q2IQ2DQ2BQ2CEEp+02IS0LD@]^]3Y0F%j0R0=2H0Q0;Q0CQ0FQ0GQ2D>0JO@p+02QS2@#ZQ2D<0J@'8P4P<Q0HQ0IQ0JQ0KPBQ2EQ2E/`KQ2EP[Q1vP]PjQ1vQ2<'1R0Q1~K1<P_PjP0PuQ1~CzPvP`Q2EP\PcQ1vH0sJ1?PzQ1SP0PjQ1~p+02:S1~P6Q0fQ1~/:0PzQ1SPcP0Q1~P{J01P{n0100000020000Q2EPzQ1S1Nc0I0rF}PnI0RP@P=P>N;14Q0Mp+02NS1S$1=+1]PSP4PTPLP4PDp+02TS1vQ1v/`KQ1vP[Q20P]Q2=Q20p+026S2A'1RnQ1uK1<P_Q2=PnPuQ1uCzPvP`Q1vP\PcQ20H0sJ1?Q1mPxPnQ2=Q1up+02<S1uP6Q0fQ1u/:nQ1mPxPcPnQ1uP{J01P{n0100000020000Q1vQ1mPx1NcnI0rF}Q1v#ZI0RPBP@EEQ1SD@[[[]W]U]V]YQ2IQ1SQ2BQ2CQ0LP[Q2=p+02GS1m20AI[RnQ0_#b$1Q$1Q$1Q$1Q$1QRx-0A[R0'8Q0>$0^S2G$0<S2J#oRzQ2J/5KRl'8S2KPnP0PzPl1yE?S2LP[Q2JQ2J#6RlH1kP[Q2JPlPxPK%6KS2MJ1^J1jQ0=$0<S2NQ0B$0<Rl+3bS0BQ2N#o%9lQ2N03alRz#o[[S2OQ2N#9R0Q0yQ2N@3`l>UWwS2PQ0y%9z[^w0S0yQ07$2kR0Q07$2HS07&3_ERl&3^ES2Q&3]ERnPn22mE?RrQ2J$0oS2R+0nPnQ2R&0oKS2RJ1g23ZnJS2SP5P=1y6123Y5=#>dB3XE?>H3WS2Tb9b:b;Q2KP5b6bDb8H0HQ29N:24P8Q2B%L[,?9S2KQ2=,?NS2UQ2=Q2=+1:S2=DRQ02P8Q2IQ2KQ2;,?NS2VCgQ2;Q2;+1:S2WPSP4PTPLP4Q0bQ1yQ2IQ2BEEQ2CD@P5P8Q1SQ2KQ2H,?NCgQ2<Q2<+1:Q2@p+02SS2XQ1yQ2DQ1SP]Q29Q2I20AI]S2Y20A]xS2Z'8Q0<$0aS2[$0^S2\$0^S2]$0<S2^#oS2_Q2^/5KR1'8S2`Q2YQ2ZQ2_P1Q2LP]Q2^Q2^#6R1H1kP]Q2^P1PxPKQ2MJ1^J1jQ0BQ2OQ2PQ0yP0Q07PlQ2QPnPnQ2^$0oR1-0nrPnP1Q2RJ1gQ2SQ2Tb9b:b;Q2`P5b6bDb8H0HPjN:24P8Q1y%L],?9S2`Q29,?NS2_Q29Q29+1:S29DRQ02P8Q2@Q2`Q2UCgQ2=PSP4PTPLP4Q2Ep+02US2=Q2@Q1yEEQ2DD@P5P8Q2XQ2`p+022R1,?NCgQ2HQ2H+1:p+02VS2Zp+02XS2YQ2=Q1vQ2XQ0_PjQ2@Q0_-0AIS2aQ0_00AxS2b'8Q2G$0a$0<S2c#oS2dQ2c/5KS2e'8S2fQ2aQ2bQ2dQ2eQ2LQ0_Q2cQ2c#6S2eH1kQ0_Q2cQ2ePxPKQ2MJ1^J1jQ0BQ2OQ2PQ0yP0Q07PlQ2QPnPnQ2c$0oS2c-0nrPnQ2cQ2RJ1gQ2SQ2Tb9b:b;Q2fP5b6bDb8H0HQ2FN:24P8Q2=Q0_#L,?9S2f1?NjS2c21:jjS2eDRQ02P8Q2ZQ2fQ2_CgQ29PSP4PTPLP4p+02WS29p+02ZS2_Q2ZQ2=EEQ1vD@P5P8Q2YQ2fQ2VCg21:11p+02[S2Vp+02]S2fQ2_p+02YS2dQ2YQ0^Q2FQ2ZQ0^-0AIS2bQ0^00AxS2a'8Q0?$0aS2g$0a$0<Rj#oS2h15jKS2i'8S2jQ2bQ2aQ2hQ2iQ2LQ0^Pj%6jS2iH1kQ0^PjQ2iPxPKQ2MJ1^J1jQ0BQ2OQ2PQ0yP0Q07PlQ2QPnPn&0ojRj-0nrPnPjQ2RJ1gQ2SQ2Tb9b:b;Q2jP5b6bDb8H0HQ28N:24P8Q2_Q0^#L,?9RjQ2F,?NQ2FQ2F+1:DRQ02P8Q2VPjQ2cCgQ2ePSP4PTPLP4p+02\S2ep+02_S2cQ2VQ2_EEQ2dD@P5P8Q2fPjQ2UCgQ2Wp+02`S2Up+02bS2FQ2cp+02^S28Q2fP\Q2V20AI\S2j20A\xS2i'8Q0>$0aS2h$0<S2a#oS2bQ2a/5KRj'8S2kQ2jQ2iQ2bPjQ2LP\Q2aQ2a#6RjH1kP\Q2aPjPxPKQ2MJ1^J1jQ0BQ2OQ2PQ0yP0Q07PlQ2QPnPnQ2a$0oRx-0nrPnPxQ2RJ1gQ2SQ2Tb9b:b;Q2kP5b6bDb8H0HL3VP8Q2c%L\,?9Q2UQ2F/C\I0GP4p+02aS2kQ2Zp+02cS2R#DQ2R/C\RxQ1UQ29Q20L3UQ1UQ2k/ax,BN'<P4Q2FQ29p+02dS1U#DQ1U/C\RxQ26Q2YQ1>L3TQ2F/ax,BNQ26'<Q2Rp+02eS26/C\'aP81BN5S1>PE&3S>1BN>S20Q20/5z+0Np+028S2MQ2C'1PEP4p+02gS2LQ2ep+02iS2b#DRxPxP1Q2;Q0`#=RxQ2fQ2fQ23N;3R%L5S23p+02hS2iQ1M+17S2j'<P4Q28Q2bQ2<Q2H3],?NP>H1[#>[^KGQ2LQ2;7]1Rj#9Q2L023x=_jz41fQ02Q23Q2bQ1=+17'<P4Q2cp+02jS2;Q2:Q2<3],?NP>H1[#>[^KGQ2iQ2H;]1R1Q2j=_1z+0NPSP4PTPLP4Q2ip+02kS2jQ2Lp+02fS2lEEQ26D@P5Q23Q2jQ0c+17R1'<P4Q2kp+02lS2mp+027Q2A3]Rj,?NP>H1[#>[^KGQ2jQ2AQ2:3]RxA_x1z+0NQ02%9jQ2mQ18+17=_jzPSP4PTPLP4Q2mp+02oS2AQ2jQ2;EEQ2bD@P5p+02nS2:p+029S2nQ2M3]#9Q2AQ1~Q2n3]Q2AQ1Q+17;_zp+030S2M14c3S2o+17Q23/<>P4Q2ip+033S2pp+02>S2qp+02=S2r3],?NP>H1[#>[^KGXGEPDQ2oQ2MQ2o1BNVRj#610PjRjePjp+02CS2sQ2='1Rj#610RjRjePjQ0BQ2OQ2PQ0y22iEcS2tQ0W#kS0WQ0V#kS0VQ0U#kS0UQ2tQ0T#kS2uQ0S#kS0SQ0R#kS0R22hEIRI'SS2v'SS2w41e3^41ePIPIQ0<$2G-22ES2xQ0X#kS0XQ0R40]P0H16'[Q07&0F=S2yPC&0FBS2zP>&0F@S2{PC&0FCS2|?xDlS2}K21Q2QPnQ0<-2gERjQ0>#lS0>Q0?#lS2~'tS305cnS31&1u7RxPnQ2h#lS2hQ2[$0aS32#lS335UnS34PxPnQ2\#lS35Q2h5UnS36PxPnQ2~9UnrS371{n2S385\nPxPnPnQ33Q2N$0o>3MENR1PxPnPn&0ocS39Q0>'iS3:Q35PxPnQ2~Q0>5hnS3;PxPnQ39/ijS3<9UnrQ3<=hn1J2fJ06J13S3=FGFGQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEX7eS3>11=>S3?,051<CD1<DF%9BS3@/83152z14cFS3A/<215F2S3BQ3AQ3A/5z+0N[[[[[[[^0E^2E^4E^5E^?E^BE^7eS3CP5Q2d/5zPXQ2HQ2nQ1mQ2dPWP@PZP}Q16PoPdQ1EO>b6bDb8b<b=41~I0jQ23Q13'<P4Q2Lp+032S2HQ2rQ1u3]S3D,?NP>H1[#>[^KGp+031S3EQ13+17Q3D?_5zXGEP>Q13Q3EQ131BNQS3F#6Q3F,0VS3GeQ3GQ2?Q2Z'1S3G#6Q3G,0PS3GeQ3GQ0BQ2OQ2PQ0yQ3>Q3CP5Q2_/5zPUQ2<Q1~p+02HS1~Q2_Q0NP@P}Q0PQ10PpPmPyO>b6bDb8b<b=41~I0jQ3EQ1up+02;3]Q13;_zQ3DPEQ2pp+035S3DP\Pcp+02ES2<H0sS3CQ2qQ2rQ1uI3KP8Q2pQ3C'aPNQ2pQ2q'aQ2r61JNH1IP8g06FFS2rp+034S2qp+036S3C/C\S1u'aQ2qp+02FS3>,4cS3G#uS3H#=S3I'a42cS3JQ1m,4cS1m,1XS3K,?NS3L9285XJ8g00]?S3M&1;5S3N&1;>S3OQ02&1;=?2>51B@=1B@>'0S3P[1B=>1B=5'0&1;@?2=>[S3QQ3P&1;B?2@=[B3J=>5P5n2001000000120000000Y0DY0CWES3PQ3MQ3NQ3OQ3Q_0D_0C]ES3MP5PNQ2rQ3Dp+037S3N/C\'aS3OQ1m#uS1m,?NS3Q42cS3RQ3LQ3OQ3Q,BNS3S61JN00CzS3TQ1~,4cS3U,1US3V,?NS3W,BNS3X,05XGEQ1m00CAS3Y1BNZS3Z/;500CzQ3X'0XGEQ3KQ3ZQ3U#uS3U00CzS3X';00Cz/05XGEQ1m14uzS3[';S3\00CzS3]Q3VQ3[';S3^1;U5'0XGERAQ3\PAQ3Dp+02@S3_p+02?S3`3]RA#610=AS3aeS3bQ3aQ3Z#6Q3Z,0US3ceS3dQ3cQ0LQ2V'1S3e#6Q3e,0XS3feS3gQ3fQ0BQ2OQ2PQ0yP0Q07Q2y?x>lS3hQ2QQ39Q0=#lRA'iS3i,tjS3j&0ou/i1S3k'~Q3i-2bEQ3k'~,~j5cnQ2SQ2Tb9b:b;X0EX2EQ1M,15Q3[';Q1NQ3[';,;5'0^0E^2EP5Q0bP^O2b6bDb8b<b=b@Q3]Q3\Q3bQ3aQ3dQ3cQ3gQ3fQ0BQ2OQ2PQ0yQ2tQ0S+0US3]Q2tQ0Q#kS0Q<1eIS1N'SS1MPIQ2t00UIS3lQ0VQ0UQ0S3^P0H16'[Q07Q2yPBPlP>Q2{PBQ2z?xBlS3mK21Q2QPnPn1{nCS3nQ2h=hn1S3oPxPnPnQ0>Q2hPxPnPnQ371{nFS3pPxPnPnQ3<Q0>PxPnPnQ2~PjPxPnPnPrQ3<-2bEQ3k'~S3kQ3k=hn1I0hJ13J06J0KJ06J0KQ2SQ2Tb9b:b;X0EX2EX4EX5EX7eXAe15@zS3k,8B1<@B%9@S3q/8FQ1A/<D15DBS3rQ1DQ3[';S1DQ1D/5z+0N[[[[[^0E^2E^4E^5E^7e^AeP5Q2c/5zS1D%9^S3sP^Q3`Q2cQ0bQ0ZP~Q19PsQ1FO;b6bDb8b<b=b@82`zI0uQ1m00CzS3\Q1mPuPzQ3bQ3aQ3dQ3cQ3gQ3fQ0BQ2OQ2PQ0yP0Q07PlQ2QPnP;P7P7PJAcn1rJ3IQ2SQ2Tb9b:b;&1czQ0x[P5b6bDb8S3tb<b=b@H2_I0jQ3KQ3[';Q3\,;X'0Q3^20C5zQ0L:0OZcS3['0XGEQ3V00CzQ3[,05XGEQ3VQ3Cp+02AS3uQ3_3]RJ#610@JS3veS3wQ3v1BN}RJ#610ZJRJeS3xPJQ2CQ2e'1S3y#6Q3y,0UR7eS3zP7Q0BQ2OQ2PQ0yQ0UQ1M'SQ2uQ2v'S/[0'[Q07PlP=Q2zP>Q2{?xBlS1MI09S3{Q2QPnPnQ3nAhnj1S3|PxPnPnQ35PjPxPnPnQ0>9UnrS3}Q3pPxPnPnQ3iQ35PxPnPnQ0>PAPxPnPnPrQ3jQ3j=hn1I0hJ13S3~J06J0KJ06J0KQ2SQ2Tb9b:b;X0EX2EX4EX5EX7eXAeS40B1FB5z1<B>Q3@/8FQ0c/<C15CD14cCS41,1DR;15;z+0N[[[[[^0E^2E^4E^5E^7e^AeS42P5Q2U/5z%9aS43Q3_Q2UQ1SPaP^Q0aPhQ15Q0rO;b6bDb8b<b=b@82`zQ3^00CzQ3VPuPzQ3wQ3vQ3xPJQ3zP7Q3tb<b=b@H2_I0uQ3X,;UP5I0jb11BNUS3XQ3\';00CzQ3K'0eQ3L,BNR;Q3KQ3bQ3aQ3dQ3cQ3gQ3fQ0BQ2OQ2PQ0yQ40Q42P5Q1DQ3sQ3`Q2cQ0bP^Q0ZP~Q19PsQ1FO;b6bDb8b<b=b@+1zI0uQ3XQ3Y';00Cz/0;eQ3SQ1m$3HI0uQ3T/0;eQ3R,BNQ3OQ3Q+3GI0uO4b1Q3JQ0NQ3G61xNR;528eQ2qQ2rQ1uQ3I43F'aQ2qQ2rQ1uQ3IH3EEYQ2qQ1uQ3H+03'a=28;R;eP;Q3DQ3_'aQ3`61JNR;#610=;P8Q3Cp+038S3`Q3U81i\'aP8P5PNQ3Np+02BS3U'aQ3u61JNR;H1IXJ8P=Q3WP>J1wP8Q3WPNQ3CQ3u'aQ3_61JNH1IP;PNP}PcQ2CH07S3_1?N5S3u528XGEP5PBP>I0uP8Q3[,?NS3[PNPBH1IP8PE&3DNQ3_1?NDR;P5J2nQ3_,BN1BN;'0Q0PQ2B80OcR;:0@NNB0@NNFS3W,05XGEP5P;p+039S3HQ2?Q2s3]S1u#6Q1u,0CS1ueQ1u1BN^S1u#6Q0ZQ1u'0S1ueQ1uQ0bQ2c'1S1u#6Q0PQ1u'0S3IeQ3IQ0BQ2OQ2PQ0yQ40Q42P5Q2R/5zQ0a#9Q2sQ2RQ2@Q0aP~PiPoQ1_PkO;b6bDb8b<b=b@-1z;I0jB0@NNC,0;Q3WQ0b:0O^cS3W/05XGEP5PFp+03:S2sQ2<Q2?3]R;#610F;R;eP;1BNaR;#610^;R;eP;Q1SQ2U'1R;#6Q0Z/0;R;eP;Q0BQ2OQ2PQ0yQ0?$2G-22ES0?Q2uQ0SQ1N'SS2?40]/[0Q07Q2yPBQ3mP>Q1MI09Q2QPnQ2G#lS2GQ305cnS30PxPnQ39Q2G'iS1M,~j=Un1PxPnAUnrjS3mPxPnQ3;PxQ3mQ3|5\nFGFGQ2SQ2Tb9b:b;X0EX2EX4EX5EQ3?,0@S3?Q0c=_>z%9=S4215BDS40Q3@15BzS3I'8[[[[^0E^2E^4E^5EP5P~Q2EQ1UPQP@PWPUQ1RO8b6bDb8b<b=b@-1zFI0jQ0ZQ2I80OcS2r/0Fp+03;S3JQ3>Q2<3]R;#6102;R;eP;1BNbR;#610a;R;eP;Q2DQ2k'1S3>#6Q3>,0^R;eP;Q0BQ2OQ2PQ0yQ2xQ0Q<0]I/[0Q07Q2yQ2{7x>Q2QPnPnQ39Q2[#lS2<'iS3G,tAR;PjPxAcnj;J0:Q2SQ2Tb9b:b;X0EX2EX4EQ1=,1>/05Q1A:0;>=[^0E^2E^4EP5Q2XQ0ePWPCO4b6bDb8b<b=b@b_b_b_b_b_c0SQ3K,0=Q2sQ3DQ2jQ2_PUQ1vQ1SQ1~Q0~P8PZP8Q3CQ2aQ0661Y9R;P5CgXJ8Q0ZQ3Z,?N23CNZEYP8Q3DP;1?NUCgePqQ0ePaQ3wQ3vQ3xPJQ3zP7Q0BQ2OQ2PQ0yP0Q07Q3hQ2QPnAhnjAS3hPxPnQ3mPxQ3mQ3h5\nFGQ2SQ2Tb9b:b;X0EX2E155>S3Z%9>S2aQ42@1F=@[[^0E^2EP5Q1SQ2UQ0rQ1BO4b6bDb8b<b=b@Q3wQ3vQ3xPJQ3zP7Q0BQ2OQ2PQ0yQ2w/[0S1BQ07PlP@Q2{P=PlP>PlK0eQ2QPnPnQ2]#lR;Q3<,tAPxPnAUnr;S2]PxPn1{nDS42AhnA1S3K5\nPxPnPnQ3<PAQ3KI0hFGJ0:Q2SQ2Tb9b:b;X0EX2EX4EX7eQ0`:0;=>Q3qQ3k,8DQ1A/<BQ3I'8[[[^0E^2E^4E^7eP5Q43P3PaQ1SPCPQP^O7b6bDb8b<b=b@Q3wQ3vQ3xPJQ3zP7Q0BQ2OQ2PQ0yP0Q07&0F>Q2QPnQ3mPxQ3mH1vQ2SQ2Tb9b:b;X0ES43%95S3qQ2a[^0ES2aP5Q2_Q1OO2b6bDb8b<b=b@Q3wQ3vQ3xPJQ3zP7Q0BQ2OQ2PQ0yQ43Q2aP5Q1vQ1CO2b6bDb8b<b=b@Q3wQ3vQ3xPJQ3zP7Q0BQ2OQ2PQ0yQ2[PEQ2xQ0<222E?H3B63AEQ0RQ0Q/SIS2[40]/[0Q07Q2zP=PlP>&0FDS0<PDPlP@PlI09I09Q2QPnPnQ2g#lS2gQ2<,tAS2aPxPnPnQ2gQ2~'i,~jP1PxQ2aQ2~'i,~j=hn1J13J0:Q2SQ2Tb9b:b;X0EX2EX4EX5EX?EB0;B>=Af>DB/5zP=P@PBPDCz/5z[[^0E^2E^4E^5E^?EP5Q0ZQ1vQ2UQ1SQ2_P@Q1RO7b6bDb8b<b=b@P@P4Q2mQ3uQ3e,4c#MH1[#>XGEPDQ1~Q2_60~c#MQ3wQ3vQ3xPJQ3zP7Q2BQ2f60~cR7#MS3z#LS3x14cZS3v'<%P7S3wQ3v'<P5XSERJQ2>$2AXXEXSES2>Q3xQ3wPJPJQ23#6XSGS3xQ3zQ3wPJ%P5XSES3zP7P7P7I0MJ1tQ3vQ3vQ3v#6L1n&0P7P7Q3wP7P7Q3wI0YQ2IQ28'1S3w,4c#PPEQ0BQ2OQ2PQ0yQ0SQ0?Q0R+0Q;^IR7PIQ0R1[70H16Q07Q3{Q2QPnPnPnQ3nPnQ39Q35Q0>'tS3{'i-1XjH0|Q3pAcnjrS3v5\nPxPnQ3{9cnAS3pPxPnQ0>Q355hnS1~PxQ3i9UnjFGJ0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX7eXAePBP511@=S1S,4c&1c5S43,8DH1111B@S3I,0=Q40Q0c,<@[[[^0E^2E^4E^5E^7e^AeP5Q1yQ2F'1S1A,4cR7$0{%o7Q1yQ2FPaP@PBPDPmO9b6b8bIbLbHH0Hb<b=b@O2Q3VP5I0jOBQ0CQ0CPLQ3CQ09,?NS3VQ2m&3?4S3kI0?PLP5Q09>1bNKS0`Q2mQ3[Q2=Q2DQ3e40v41_Q3kI0?61W4P8Q2JQ0661Y9S2J,d5S3KPNQ0LH1IP8Q2^Q0661Y9S2^,d5S0LPNQ2=Q3eQ2DH0lP8Q32$0^S3<$0<Q0661Y9S1=,d5S3QPNQ2=Q3ePuQ2DPvJ0}P8Q32$0aS32$0<Q0661Y9S3e,d5S3OQ3[&1;9R7Q2J:1D75S3[Q2^:1D7>S3RQ1=:1D7=S3TQ3e:1D7@S1mP81dDBS3SQ3JPBH2@[[[[]CH2?K2J41fWr+3>Q03Q0CQ0CPLQ3NQ3Vp+02mS03Q3kI0?PLP5Q0`Q03Q3_Q2ZQ1yQ3y40v41_Q3kI0?61W4P8Q3KPNQ2CH1IP8Q0LPNQ2ZQ3yQ1yH0lP8Q3QPNQ2ZQ3yPuQ1yPvJ0}P8Q3OQ3_Q3[Q3RQ3TQ1mP8Q3Sp+03<S3_PBH2@[[[[^C7H2?K2J41fWrPSP4PTPLP4Q3NQ2sQ3CQ3DEEQ2qD@P5Q0CPLQ3HQ3VQ2AQ3kI0?PLP5Q0`Q2AQ2r,?NS2rQ2YQ2EQ3w40v41_Q3kI0?61W4P8Q3KPNQ2IH1IP8Q0LPNQ2YQ3wQ2EH0lP8Q3QPNQ2YQ3wPuQ2EPvJ0}P8Q3OQ2rQ3[Q3RQ3TQ1mP8Q3Sp+03>S3SPBH2@[[[[^C7H2?K2J41fQ02PLQ2sQ3VQ2MQ3kI0?PLP>Q0`Q2MQ3W,?NS3WQ2dQ2XQ1u40v41_Q3kI0?61W4P8P>Q2JQ0b,?NP8P>Q2^PNQ2dQ1uQ2XH0lP8P>Q1=PNQ2dQ1uPuQ2XPvJ0}P8P>Q3eQ3WQ3[Q3RQ3TQ1mP8PCPBp+03?S3WPBI0d[[[[^C7DRDRDRDRPSP4PTPLP4Q3JQ3SQ2sQ3HEEQ3`D@P5PLQ3_Q3VQ2HQ3kI0?PLP@Q0`Q2HPNPbPcQ2DH07Q2VQ2=Q3>40v41_Q3kI0?61W4P8PBQ2JQ1y,?NP8PBQ2^PNQ2eQ1AQ2ZH0lP8PBQ1=PNQ2eQ1APuQ2ZPvJ0}P8PBQ3ePNP~PcQ1yH07Q3[Q3RQ3TQ1mP8P3PBp+03BS1yPBI0d[[[[^C7DRDRDRDRQ02P8PDQ2JQ2@,?NCgP8PDQ2^PNQ2fQ2@Q2R'1S2ZQ29H0lP8PDQ1=PNQ2fQ2ZPuQ29PvJ0}P8PDQ3ePNQ0aPcQ2@H07Q3[Q3RQ3TQ1mP8PRPBp+03CS2@PBI0d[[[[^C7DRDRDRPSP4PTPLP4Q3WQ1yQ3Sp+03=S2ZEEQ3_D@P5P8PFQ2JQ2X,?NCgP8P2Q2^PNQ2UQ1vQ2l'1S2XQ2_H0lP8P2Q1=PNQ2UQ2XPuQ2_PvJ0}P8P2Q3ePNPiPcQ1vH07Q3[Q3RQ3TQ1mP8PQPBp+03FS1vPBI0d[[[[^C7DRDRDRQ02P8P3Q2^PNQ2kQ2=Q2L'1S2XQ2VH0lCgP8P3Q1=PNQ2kQ2XPuQ2VPvJ0}P8P3Q3ePNQ0sPcQ2=H07Q3[Q3RQ3TQ1mP8PWPBp+03GS2=PBI0d[[[[^C7DRDRPSP4PTPLP4Q2@Q1vQ1yp+03AS2XEEp+03@S1AD@P5P8PPQ2^Q2RQ29Q2bQ2f3q61bNCgP8PVQ1=PNQ1UQ2YQ2;<1GuQ28PvI2>P8PVQ3ePNPqPcQ2YH07Q3[Q3RQ3TQ1mP8PUPBp+03JS2YPBI0d[[[[^C7DRDRQ02P8PQQ1=PNQ26Q2dQ2j<1GuQ2cPvI2>CgP8PQQ3ePNPfPcQ2dH07Q3[Q3RQ3TQ1mP8PZPBp+03KS2dPBI0d[[[[^C7DRPSP4PTPLP4Q2=Q2YQ1vp+03ES29EEp+03DS3>D@P5P8Q0NQ1=PNQ2LQ2VQ03<1GuQ2kPvI2>CgP8PXQ3ePNQ10PcQ2eH07Q3[Q3RQ3TQ1mP8Q0ZPBp+03NS2DPBI0d[[[[^C7DRQ02P8PUQ3ePNQ0~PcQ2fH07CgQ3[Q3RQ3TQ1mP8P^PBp+03OS0`PBI0d[[[[^C7PSP4PTPLP4Q2dQ2DQ2Yp+03IS3VEEp+03HS1uD@P5P8P}Q3ePNQ1JPcQ2cH07CgQ3[Q3RQ3TQ1mP8P~PBp+03RS0bPBI0d[[[[^C7Q3>PNQ19PcQ2kH07Q03Q2LQ2kQ2p'140v41_Q0FQ0bp+03PS3[Q3[Q0`Q2Dp+03MS3Rp+03LS3TQ0b#mS1m/;KQ0bP[Q2FP]Q2:Q17Q2iK1<P_Q2:Q17PuQ2iCzPvP`Q0bP\PcQ2FH0sJ1?S2rQ2VQ2_Q17Q2:Q2iQ2sP6Q0fQ2sQ17':Q2VQ2_PcQ17Q2sP{J01P{n0100000020000Q0bQ2VQ2_Q1|#=I0rF}Q0b#ZS1|P^P5Q2dQ2nQ1|Q3[+2=Q09PLQ3[Q3uP<Q0Jp+03QS09p+03SS1|Q2DQ0`J2FQ3kI0?PLPaB1bN5KP>Q3kI0?61W4XGEPZQ1mQ3WI0uQ3[Q2rP^Q06:1Y9?S06:1D75PMP6PM%V>S2r/K`p+03TS1mQ1U,4cS3k81Z\S2DQ2rQ1m$0wS2nQ1U#=S2_7J[S3OQ2MQ2;81`hS2E7J]S3wQ2MPhPuQ2;PvDvS3Q7J_S0L%=?R?40LS2In0100000020000P81d~=S3KQ1|P5H1aXRMPMP6PMQ2r/K_Q3QQ2rQ3w<0L?S3yn0100000020000P8Q3KQ1|P6PM%V=S2C/K`S3Xp+03US3YP\PcQ26H0sS3sP5n0100000020000H1aXRMPMP6PMQ2r/K]Q2EQ2rQ3O<0L?S1Dn0100000020000P8Q3KQ1|P6PMQ3XQ3sP6PMQ2C/K_S3fQ3EQ1EPuQ2jPvDvS3gP5n0100000020000n0100000020000H1aXRMPMP6PMQ2r/K[Q2_Q2rQ2n<0L?n0100000020000P8Q3KQ1|P6PMQ3XQ3sP6PMQ3fQ3gP6PMQ2C/K]Q3EQ1EQ2j41`S2CP5n0100000020000n0100000020000n0100000020000H1aXRMP4P<Q0HQ0IQ0JQ0KQ0bQ1mQ09Q3[Q0`Q3RP>N=3<P8Q09P>Q0bQ2n03;>I0GQ02Q0n$0=Q0o#sS0o[Q0p#sQ0q$0=[S0qQ0o21K@=$0=[239>5P5n2001000000120000000XXEXSEQ0q^XE^SEP51B9@S0qQ06,B9S0oQ0qQ0o'0S0oP@Q3PQ3MP5P9PDQ06P>O4b1O1Y0VQ0o#seO3b1Q06:2Z9=$0=S0oeQ0oP6Q06:2Z9@P8Q1mPBQ3YP6PMP5P?%VBS06p+03WS0o$0w<0L?n0100000020000I0GXJ6P>Q08P5J1wP8Q1|P@Q1m%V@p+03VS3M$0w<0L?I0GQ06/K`P6Q0O%VD/K`/|5P6%VFS06/K`/|5P8Q0uP2p+03YS3PP6PMP>p+03[S0qP\PcQ2jH0sP6PM%V2S0n/K_S0`Q3NQ1FPuQ3EPvDvP6PMQ0n/K]Q3NQ1FQ3E41`P6PMQ0n/K[Q2j#=Q0nQ0q$0w<0L?n0100000020000n0100000020000n0100000020000n0100000020000I0G]]P>%VC/K`S3f#>Q021K>5S3X#>1T=>S3K[S3c1T>5S3d1K=>S3a#>S3b[Q3b1T@=S3L[238>5P>n2001000000120000000XKGXEGS3bQ3c^KG^EGS3cP5Q0nP`P>O3Q0n/T`P7%L`,?9P8PqP5Q0qp+03]S0nQ03,4cS3\81Z\S3tI0GXC7P8Q11Q3e'dQ2m,4cS3^:1xNmS44p+03ZS45p+03\S46Q3^81Z\S3^'aS47PVP8Q44Q3\:1xNkS3\=285XJ8Q44,y8Q47Q10EYJ1mP3B1r3`5EYb]b1W]Q3f$0=Q06/K_P6Q0OQ0`/|5P6%VRS0`/K_/|5P8PfPPQ46P6PMP>Q2sPmPuQ2qPvDvS06P6PM%VPS3f/K]S47Q2sQ2q81`mS48P6PMQ3f/K[Q2:#=S49Q3fp+03^S4:$0wS4;<0L?n0100000020000n0100000020000n0100000020000I0G]\P>%V3/K_S4<#>Q3bQ3cP5Q3fP_P>O3Q3f/T_P7%L_,?9P8Q16P5Q4:Q3_Q1RPuQ3CPvDvI0GXC7P8Q0|Q1='dQ3JQ2AQ2X'1S16PuQ3DCzS3f00gvS4=,?NS4>Q0nQ3JQ3D9qku<1EvR9#=S4?'aS4@P}1?N9,y8Q4>Q4@528eJ1mPVB1rV_5EYb\b1W\Q4<$0=Q0`/K]P6Q0OQ47/|5P6%VQS47/K]/|5P8Q10PWp+03_R9P6PMP>Q2ZQ1@Q3N41`P6PM%VWS0`/K[S4<Q3E#=Q0`p+03aS4@$0w<0L?n0100000020000n0100000020000I0G][P>%VV/K]S4>#>Q3bQ3cP5Q0`P]P>O3Q0`/T]P7Q2`P8Q0dP5Q4@Q3WQ3H81`sI0GXC7P8Q0~Q2^'dPNQ3SQ2HQ3>'1S4@Q3`H0lS2`p+03`Q3SQ3`7f:S0`#='aS4AQ0aQ0`,?N,y8Q2`Q4A528eJ1mQ0NQ0N@1r]5EYb[b1W[Q4>$0=Q47/K[P6Q0OQ4</|5P6%VX/K[/|5P8Q1JPUp+03bP6PMP>Q2q#=%VUS4<p+03dS47$0w<0L?n0100000020000I0G]ZP>Q0N#V/K[S4>#>Q3bQ3cP5Q4<P[P>O3Q4</T[P7Q2KP8Q19P5Q47Q3C#=I0GXC7P8Q17Q2J'dQ3D,?Np+03cS47Q3D#='aS2KPqQ2K,y8J1mPZB1rZ[5EYbZb1WZQ4>$0=Q02Q3X$0=Q3K#s[S3KQ3d#sQ3a$0=S3a[Q3aQ3L#s[236>5P>n2001000000120000000XXGXSGS3aQ3K^XG^SGS3KP5Q4<P`PRO3Q4</T`#sQ3aQ3KP5%V}S4<P_P3O3Q4</T_#sQ3aQ3KP5Q0Z#VS4<P]P2O3Q4</T]#sQ3aQ3KP5%VaS3KP[PFO3Q3K/T[#sP8p+03h/dbP8P5p+03j%V~p+03l$0w<0L?H1aXJ8Q0P1dpbQ0aPbQ2J927bS0aP>P7Q2J%V5S2J/T[XC71yG[P~P5EYO1WlQ0a#seQ2^927bS0aP@P7Q2^Q2J/T]XC71yG]P~P5EYO1WlQ0a#seQ1=927bS0aPDP7Q1=Q2J/T_XC71yG_P~P5EYO1WlQ0a#seQ3e927bRbPFP7Q3eQ2J/T`XC71yG`P~P5EYO1Wl%sbeO5EYbZb1b[b1b\b1b]b1WZn0110200020101P5O1bZbJW[n0110200020101P5O1b[bJW\n0110200020101P5O1b\bJW]n0110200020101P5O1b]bJbvc0cbvQ1DP[Q2nQ2_Q2rH1qEYQ3yP]Q3OQ2EQ2rH1qEYQ2IP_Q3wQ3QQ2rH1qEYQ2rQ0LQ2D7J`<0L?P`Q0LQ2DQ2rH1qEYY0bXC7H35Q2:Q2iQ2FQ2q'1#MR7433Q0DQ2:Q2iP7H34Q0TQ17#M+0z'TR7eP7Q1EQ2R80OcS2rQ3k:1xNyS3k,BN/05XtEQ2rQ09Q2eQ2V3]R7#6Q0s/07R7eP71BNoR7#610y7R7eP7Q26Q3N'1R7#6Q1E/07R7eP7Q0DQ2HQ2mQ2lQ3`'1S2VH0WR7Q0TQ1a+0zR?'T%L7Rb%Py,4c'0R~&2XGS2D&2XES0L%L>Q23'0Q3d232>5431XXGXSGS3dP7Pb%6bP?Q3zPyO1R?,4cQ0TPc%6cS3QQ1aP?PJQ3zPyPyPyI0MJ0kN91OP@H1MP~Q0DQ2pQ03Q2LQ3H'140vS1a+1pS3w$1SQ3w#LR~#9&0PpPp%PpR?PpPpP?I0Y%PtS2IPEQ0BQ2OQ2PQ0yQ3`Q2mQ3S'1S2EPuQ2HCzR?00yv%9?%9vR?Q2sQ2:Q1A'1S3OQ2q7qu<1Ev#9[[Q0VQ2u/SI+0fRbQ0SQ2tQ0R+0US3yQ1N'S+0fR7B0[7b040[Q07PlPCQ0<P=Q2zQ2|7xCP>Q2{?xClK0eQ2QPnPnPnPnQ2G-0nrQ38H2VPnPnQ2GPr1{n3R7I0hPxPnPnQ2GQ0>,tAPxPnQ3<#lS3<9cnjS0>PxPnQ3j9cn;PxPnPnQ1M>2^;1PxPnQ2]PxPn1{nRS1MQ3|5\nPxPnPnQ3}1{nPS3jPxQ3~J0KFGI2dFGJ0:J0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEX7eXAeXPeXQe%o@S3~&0{@S2G/8F81oCB0;B=@10=FQ0c:0;F@Q3A,;2S1N/<z%93RbB1FWCz18bX15R3Q13,13S2_Q2_/5z+0N[[[[[[[[[^0E^2E^4E^5E^?E^BE^7e^Ae^Pe^QeP5Q1A/5zQ1R#9&1cBS2_10BmQ1@,BNS2nQ17PmQ1AQ2:Q1RPDP2P3Q0~Q19PyPkQ1rQ1lOCb6b8bIbNbLbHbObMb<b=b@+1zQ0sPgI0uQ2r:0@NNQ0s'0Q05Q0b>1y4=S2rQ2fQ2ePhQ2MQ2;Q3_#MS1lJ1|S1rP6Q0fQ3_/:hS0~Q2fQ2e+0_S1DPcPhQ3_P{DwP{n0100000020000S2JQ1m#DS3eQ2fQ2e1NchS0aH19S1=+1{S2^Q0bQ2=Q2fQ2ePhQ2MQ2;Q1lQ3kP5Q0bQ1D+1LS1D#6Q0uQ1D'0S1DeS1lQ1D1BNpS3K#6Q3K,0oS3KeS3aQ3KQ2V#6Q2V,0yS2VeS4<Q2VQ3W#MS3L%MoS3X+2~Q3W#PS02%PoS4>'<Q3LQ02PJQ3zQ3WQ3WQ3WI0MQ3XQ4>PJQ3zPoPoPoI0MS02J2}Q3wQ0TQ3X+0zS3L'TQ4>,4c,0~S4>Q2DQ0LQ3dQ3wP~%6~Q3LQ3zPoO1R~,4cQ0TPcQ3QQ3XP~Q02J0kN91OPBH1MS02Q4>Q0DQ2qQ2:Q2iQ2s'1S3XH0WR~$1SS2K%L~#9S3c&0PtS3bPtQ2IPtPtQ2II0YS4A%PwS2`PEQ2@$0PQ2@Q2@#PR~Q2@Q2@P~I0YQ3>#PPEQ0BQ2OQ2PQ0yQ3f00yvS0`Q3f#9Q2ZQ3EQ2@'1S3fQ3N7qu<1Ev#9\?[S4BQ0UQ2xQ0SQ0Q40]S4C+0fR~Q0VQ0UQ2xQ2u+0QS4D;^I+0fQ0VQ4DQ2v3^22E~0'[40[Q07PlPCQ2|P=Q2zP>Q2{PCQ0<PCPlI20K0eQ2QPnPnPnQ38Pn21Xj;H0|Q3v9\n7PxPnPnPnPnQ2h-0nrQ2h9cnAS38H2VS4EQ2h=UnrS4FAcnArS4G5\nPxPnQ2hQ3{5cnS4HPxPnQ2h9Un;PxPnQ1~PxAUnjAH1vFGJ0DJ0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEX7eXAePCP5PDQ43,8FH1110=DS4I-2|DS4J&0{DS4K02U=S4L+00B0;CDBS4M1<2F15CF1<DC[[[[[^0E^2E^4E^5E^?E^BE^7e^AeP5Q3V$0{Q3V#oQ3VQ1@Q3EQ2@PCPBPDPFPRQ1cQ1xO=b6bIbNbpbsbnbLbHbObMH0Hb<b=b@Q1lQ1DQ3aQ3KQ4<Q2VQ02Q4>Q2KQ3cQ3bQ4AQ2`PEQ0BQ2OQ2PQ0yQ3HQ03Q3W'1S1cPuQ2pCzR~00yvS4N%9~Q4=#9\?[S4=Q2xQ0R+0QS4OQ0Q5^I/[0Q07Q2yP@PlP>Q2{P@PlK21Q2QPnPnAhnrjS4PQ425\nAUnjrS42Q3n5\nPxPnQ31PxPnQ3;PxQ4PFGJ0DQ2SQ2Tb9b:b;X0EX2EX4EX7eXAe%o5S3n&0{5S4Q/8B81o@Q1S,0>S4R15@BQ3~[[[^0E^2E^4E^7e^AeP5Q2_10BkQ2AQ2XPkPDP2Q1iO8b6b8bIbNbLbHbObMb<b=b@Q1lQ1DQ3aQ3KQ4<Q2VQ02Q4>Q2KQ3cQ3bQ4AQ2`PEQ0BQ2OQ2PQ0yQ4NQ4=Q0?Q0WQ0=$2G-22ES0=Q0VQ4DQ0SQ0R3^40]40]PIQ2tQ0X+0US3~Q0WQ2xQ0V+0QS4SQ0UQ2N-2iES2NQ0RQ0Q41eS4TI1NP0H16Q07PlPFQ0<P=Q2zP>PlP@Q2|PF&0FFS4U9xlFS4VI09K0eQ2QPnQ3pPxPnQ32#lS329cn;S3pPxPnQ2\$0a#lR~=cnjS2\PxPnQ39Q35'iS4W,t;9cn~PxPnQ3i,~~=Un1S4XPxPnAhn;1S4Y9\n7PxPnPnQ3}Q1MPxQ3i,~j=Un1S4ZJ0KFGFGFGQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEX7eXAeQ4R10DF10F=Q41:0;2FQ18=_3z153zS18,8V%92S4[/8WQ1Q=_Fz[[[[[[[^0E^2E^4E^5E^?E^BE^FE^7e^AeP5Q2X/5zQ1@#91BN:Q19Q1@Q2AQ2XPkQ0nQ2iQ2L+0_S4\+1LS4]P2P3PRQ0dPhQ1RQ1sO@b6b8bIbNbLbHbObMb<b=b@Q1lQ1DQ3aQ3KQ4<Q2VQ02Q4>Q2KQ3cQ3bQ4AQ2`PEQ0BQ2OQ2PQ0yQ4NQ4=Q1BQ07Q2yPDQ2z?xDlP>PlP@Q0<PDPlI09I09Q2QPnQ30PxPnQ2\PxPnAUnr~S30PxPnQ3;PxQ3mFGFGQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EQ3?10D>%9CS3;Q40Q3@[[[[^0E^2E^4E^5E^?EP5Q19PkQ2AQ2XQ4]P2PRPoQ1iO9b6b8bIbNbLbHbObMb<b=b@N>2{Q05Q2rQ1r42TeQ05Q2rQ2JQ1=Q0~P6Q0OQ2ZQ1E':S0O/|5P6Q3W/:o/|5Q0;Q0CQ0FQ0GQ45>0JO@Q46#ZS0~Q45<0J@'8P4P<Q0HQ0IQ0JQ0KPBQ0nQ0n/`KQ0nP[Q03P]Q3HPdQ2pK1<P_Q3HPdPuQ2pCzPvP`Q3tJ1?Q2lQ26PdQ3HQ2pQ29P6Q0fPCQ2lQ26+0_S3tPcPdQ29P{DwP{n0100000020000Q0nQ2lQ26Q1o#=I0rF}Q0n#ZI0RP@P=P>N;14Q0MQ3P$1=+1]PSP4PTPLP4PDP91`9KP9P[Q2AP]Q3JPkQ3DK1<P_Q4?P`P9P\Q2A,4cS4?#uK2jQ2iQ2LPkQ3JQ3DQ2=P6Q0fP2Q4\PcPkQ2=P{DwP{n0100000020000P9Q2iQ2LQ25#=I0rF}%Z9I0RPBP@EEQ3PD@[[[]W]U]V]YQ05Q0o>1y4FP6Q0fP=Q2FQ2kPcPtQ2XP{J01P{n010000002000042T]^]dP>Q3S/:yS25#>Q0;Q0CQ0FQ0GQ3P>0JO@Q0q#ZQ3P<0J@'8S4\P4P<Q0HQ0IQ0JQ0KPBQ46Q46/`KS0nQ46P[Q2mP]Q3`Q0rQ2HK1<P_Q3`Q0rPuQ2HCzPvP`Q3^J1?S3^Q26Q1UQ0rQ3`Q2HQ3>J25S2mQ26Q1U+0_S1oPcQ0rQ3>P{DwQ46Q26Q1UQ1}#=H2SS1}418Q0~I0RP@P=P>N;14Q0Mp+03XR9$1=+1]S0MPSP4PTPLP4PDQ4:Q4:/`KS1=Q4;P[Q49P]Q48I1dP_Q06P`Q4:P\Q2:,4cS06#uK2jS48Q2LQ2lPmQ2sQ2qQ1vJ25S49Q2LQ2lPcPmQ1vP{J01Q4:Q2LQ2l1NcmH2SS2l418Q4:#ZS4;I0RPBP@EEP9D@[[[]W]U]V]YQ0}Q24P5Q2XPtP=O3Q2X/5tQ05B1y492S24Q2RQ2F+0_RhQ1y:0~cwS2F#=S0}+2KS2JP{Q2FQ3PQ1UQ2R+0_<2l5Q3qQ3Z'8Q0EPPQ0qQ3t+1LS3t>1bN>O1Q0D$1uS0q41D[^mE'8XGEQ2F:2l9hS3ZQ3qQ1FQ2@60~c81F5S3qQ0EPRQ45Q1o+1LS1o>1bN>O1Q0q41DS45[^mE21L9hRh#6Q10/0hS10eS3PQ101BNmRh#610dhS2reS1iQ2rQ2E#6Q0rQ2E'0S2EeS4]Q2EQ0DQ3HQ2pQ1c40vS1c+1pS3?Q0T%MdS40+0zS3@'TQ3?#LRh%PdS2y,4c'0S1BQ2DQ0LQ3dQ3?Ph%6hQ3@Q3zPdO1Rh,4cQ0TPcQ3QQ40PhPJQ3zPdPdPdI0MJ0kN91OPRH1MS40Q1BQ0DQ2sQ2qQ3OH0WRh$1SS2q%Lh#9S4=&0PkS4NPk%PkS4APkPkQ4AI0YS3bQ1R#PS3cPEQ0BQ2OQ2PQ0yQ3WQ2pQ29<1GuQ3H3fRh00yvS2p%9hQ2XQ3DQ2='1S2KQ3J7qu<1Ev#9\?[S4>%k_RhQ2xQ0[#kS0[+0QS02Q0XQ2v3^+0fS2VQ2x00QhQ0[Q0Y#kS0YQ2tQ0V+0US4<Q2?'S3^+0fS0[Q0V,SI-2LIS2?Q0?Q0\#kS0\Q0=%k`S3KQ02%k]%k[S3a3^40]40]PIQ2tQ0]#k+0UQ0\Q2xQ3K+0QQ2NQ0W+0UQ2tQ0U+0US3KQ0Q'SS0\5^hI1N+2LRhQ2?Q0[Q2V<0[060[h40[40[Q07&0FPPCPlPV&0F2S2?I09P=Q2zP>&0FVPFPlPV&0F3P@&0FR9xlDK0eI09Q2QPnPnPn1{nWS0[PnQ0@$0a#lS2V01XAH0|PnPnPAPrQ0N,{nI0hPxPnPnPrQ0A#lS0APxPnPnQ0AQ39Q2V'iPxPnPnPAQ33Q35'tS0]PxPnQ3pPxPnQ2\PxPnPnP~Q39Q33'iS2\,t;PxPnQ4XPxPnQ30PxPnPn1{nXQ4YPxPnPnP;Q2gPxPnPnQ0@#lRhP;PxPnPnQ339Unr1{nUPxPnPnQ359UnrS0@1{nZPxPnPnQ2<PAPxPnPnPrQ2<PxPnPnQ2gP1PxPnPnQ2\PhPxPnQ35Q335hnS35PxPnQ3mQ3|PnPnPrQ39Q2a'iS2aQ2a,~j=Un1I0h5\nJ2fJ06J13J06J13J0KJ0KJ06J06J0KFGJ0:FGJ0:J0:J06J0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEXaEZ0BEZ0?EZ0@EZ0AEX7eXAeXPeXQeX`ePVPPP>23[>QH11%9P14cQ,0VB0;BFC10PQ10QDQ13:0;WQQ0NQ1Q;_z%9XS1QB1FaXz1<UX1<XZQ1Q/8gQ1Q/8iQ0N,5X%9U15^zQ1Z/<^Q0Z/5^15}zQ0PQ0Z60~cR^#9A_}^z41f-0N}[[[[[[[[[[[[[[[[[[[^0E^2E^4E^5E^?E^BE^FE^aE`0BE`0?E`0@E`0AE^7e^Ae^Pe^Qe^`eP5Q2=/5zS1ZQ3D/5zQ1_#9Q2_Q1X#oPBQ0DQ2XQ3JQ2KH0W#LQ1C,BNPtQ1_Q2kQ2LQ3DQ2=Q3RQ1XQ47Q2:Q033]PDPCPFP2P3PRPyPwPdQ1OQ1WQ1:Q1]Q1PPPp+01YS47Q1{Q22Q1TOTb6b8bIbNbLbHbObMb<b=b@Q3ZeQ3qQ1o#6Q0dQ1o'0R^eP^Q1R,BNR^#610k^R^eP^Q3O#6Q3O,0mRmePmQ1@Q4?'1:0@NNRm%MBS4?#LS3O';S1oQ19/;BR^'0%PBRa,;mS3Z/0^PEPEQ0LPJQ0LQ0p$2AXXEXSEQ1oQ3ZPJPJPJPEPEg02=71;>5H3\#6XKEXEES3ZPmPm%6mQ3OPaPJPJQ3xQ4?PaPJQ3zPBPBPBI0MJ1tN:2RP^P^%6^N<1\Q0DQ3JQ3DQ16H0WR^Q0T%MkS4?+0zRa'T%L^RmQ4A,4c'0S4AQ2DQ0LQ3dP^Pm%6mPaQ3zPkO1Ra,4cQ0TPcQ3QQ4?PaPJQ3zPkPkPkI0MJ0kN91OPVH1MQ4AQ0DQ3_Q3CQ2MQ1y'1S4AH0WRa$1S%LaRm#9&0PCPC%PCR^PCPCP^I0Y%PFPE&0PsPs%PsS4?PsPsQ4?I0YQ15#PPEQ0BQ2OQ2PQ0yQ2@Q3NQ3V<1GuQ2Z3fR^00yv%9^Q29Q3HQ2d'1Q3W7qu<1Ev#9\?[Q0VQ2xQ0U+0QS29Q4O;^IR^'SQ0UQ2w'SQ0UQ2v'S1[^0'['['[Q07Q2|PBPlP=PlP>Q4VQ0<7x@K0eQ2QPnPnPnP7PnQ2~-1XAH0|PnPnQ2~PrQ4GI0hPxPnPnP~Q33,thPxPnPnQ37Q1MPxPnPnPjQ2<PxPnPnQ33PhPx1~jAQ2<Q2~'~5cnJ13J0:J0KJ0:J0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEX7eXAePFP>P@Q2G&1c>S2~'8H11B0;FCD20NDRS2G10@D15231;DC1;F2'0[[[[[^0E^2E^4E^5E^?E^BE^FE^7e^AeP5Q1WQ0960~c,5W%oWQ1WQ3HQ2dPWPdPCQ1gQ3H80Oc:0@NNPFPRPQQ0ZQ27O>b6bIbNbpbsbnbLbHbObMH0Hb<b=b@Q44%M>#L61JNQ0d/;>'0Q3\%M=Rd#L61JNQ0EPVQ3uO1Q0q41DXGEQ1cQ3[Q3\PdPGQ3@Q1RQ06'1:0@NNQ23;_zXEGQ3t#6Q1JQ3t'0S3teS06Q3tQ2n#6Q1RQ2n'0S2neS3\Q2nQ16#6Q16,0kS16eS3[Q16Q2M:0O:c:0@NNRkQ0TQ1R#MS1c+0zRd#LS0q';S0E/<zQ3c,4cR^,;kS3u/<zPJQ2>Q0EQ3uPJPJPJQ3ZPkPk%6kQ0qP^PJPJQ3xPdP^Q0TPcQ3QQ1cQ3cPJQ3zQ1RQ1RQ1RI0MS0qJ0kS3uJ1tN:2RPzPz%6zS0EL1n1Tad10m^RkQ2DQ0LQ3dPaPm%6mPdQ3zQ1RO1Rm,4cQ0TPcQ3QQ1cPmQ0qJ0kN91OPQH1MS0qPkQ0DQ2ZQ3NQ3fH0WRm$1SS3f%Lm#9S1c&0P:S1R%o:S0d%P:RmP:&0{:S4402UmH11S0ZQ4?PEQ0BQ2OQ2PQ0yQ1yQ3CQ1u<1GuQ3_3fRm00yv%9mQ3>Q3`Q2Y<1GuQ3S3fRm00gv#9\?[Q2tQ0Y+0US1yQ0WQ0VQ2uQ3]Q2['SI1NQ1yQ3~Q0WQ0VQ0UQ3y/SIS3y'SI1N/[0'[Q07Q0<?x2lS3HP=Q2?9xlBP>PlP@Q4UP2Q2|P2PlK21I09Q2QPnPnPnQ1MQ38Q3jQ4G5\nI4<S4GPxPnQ4HPxPnQ0>PxPnQ3<Q4W,t~5cnS38PxPnPn1{nVS2dPn20n~1H0|S4VPxPnAUn~hPxPnQ0@1{nQ5\nS0@PxPnQ3}Q0[5\nS0[PxPnAhnh1S2vPxQ4ZH1vFGFGFGFGQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEXaEX7eXAeXPeXQeX`eP2P>PDQ2~,83S2~H11Q3I,0C10=3Q41:0;R3B1FWRz1<P318bU18b}15VzS41Q13=_3z[[[[[[[[[^0E^2E^4E^5E^?E^BE^FE^aE^7e^Ae^Pe^Qe^`eP5Q2Y/5zQ3`/5zQ1:#9Q1C$0{Q1C#oQ0rQ1:Q1CQ1UQ3`Q2YPBQ1:Q3`80Oc:0@NNPDP2Q0PPtQ1WQ1]Q1eQ1VQ1nOFb6b8bIbNbLbHbObMH0Hb<b=b@Q3?PREYPGQ3@%M@00A5XEGQ06Q3tQ3\Q2nQ3[Q16%MDR}00Ad%PDRa/5^P}PaPJQ3zPDPDPDI0MPdP^Q3uJ1^Q0qPkQ3fQ1cQ1RQ0ZQ4?PE&0P3P3%P3RkP3P3PkI0Y%PRPEQ0BQ2OQ2PQ0y20ymv%9mQ1vQ2sQ3T'1Q1A7qu<1Ev#9\?[Q0UQ4DQ0Q'S+0fRmQ0WQ4<Q0?Q0U+0QRk;^I+0fQ0WQ0S/SIS0?7^kPIQ0S22Em0H1640[Q07Q4UPFPlPFQ2|I09P=Q2zP>Q2{PFQ0<PFPlI20I09Q2QPnPnPnP7PnQ0A-1XjH0|Q1MQ3v5\nPxPnPnQ4EQ4FQ3j5\nPxPnQ4HPxPnPnQ2dPnQ0AQ39Q2h/t;'i+0nH0|PxPnQ2]PxPnQ1~PxQ3i9hnjFGFGJ0DJ0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEX7eXAeXPeXQePFP5PCQ43,82H11Q4JQ4K<4;RQ4MB0~cF2:1FQ3Q3BQ3A,5C[\b[[[[^0E^2E^4E^5E^?E^BE^FE^7e^Ae^Pe^QeP5Q0N#9&1cCQ0N$0{Q0N#oQ0NQ0bQ1:Q2sQ3TPCPBPDPFPRPWp+01^Q1nOAb6bIbNbpbsbnbLbHbObMH0Hb<b=b@Q3?PREYJ4:Q1J/;=P5I0jb1Q45eY0aZ13EH2yQ0}-239Q2FQ3PQ10Q1iQ2rQ4]Q2EQ40Q1BQ2qQ4=Q4NQ3bQ3cPEQ0BQ2OQ2PQ0yQ2pQ4>PIPIQ0UQ3~Q0WQ0VQ3KQ3]Q0RQ2[3^I1N/[0H16Q07Q2|PFPlP=Q2zP>Q2{PFQ4UPDPlI20K0eQ2QPnPnPjQ3{PxPnPnQ2hPhPxPnPnQ33Q2hPxPnPnQ3}P7PxPnPnPAPjPxPnPnPrPAPxPnQ2vPxPnQ4WQ335UnPxPnPnPrQ391tjA'iRhAhnh1I0hFGJ06J13J0KJ06J06J0:Q2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEX7eQ1S,051<FC1<C2Q2GQ3rQ3;15PzS1SQ13/<PB0~c23Rh15hz+0N[[[[[[[[^0E^2E^4E^5E^?E^BE^FE^7eP5Q1ZQ1_Q2kQ2LQ3DQ2=Q3RQ1XP2Q1WQ1:Q1PPPQ47Q1{Q22O@b6b8bIbNbLbHbObMb<b=b@61~9I0uP4P9P2Q2JH49eQ05Q24+2xJ48bdb1W^WdQ25$0=Q0;Q0CQ0FQ0GQ4\P4P<Q0HQ0IQ0JQ0KPBQ46Q0nQ3^Q2mQ1}818{Q0~I0RP@P=P>N;14Q0MPSP4PTPLP4PDQ4:Q1=Q48Q49Q2l818{Q4;I0RPBP@EEP9D@[[[]W]U]V]YQ05Q3M>1y4C+2xW^Wdn0110201020101P5Q1qO2bdbJQ0bQ2=P=Q3eQ2fQ2eQ0aQ1uQ1>Q1|Q28Q2f+0_S1u+1LR9'5Q1|Q21#=S21+23Q1>5_9+00Q1m14cyR9+171BN=RhQ3YQ2UQ2c3]Rm'5A_m5h+00XGEP5P9Q1mQ1mQ2cQ283]Rh#610qhRkePk1BNwRk#610tkRkePkQ3X#6Q3X,0pRpePpQ0DQ3DQ2AQ2bQ3J'1RpH0WRkQ0T%MtR^+0zRd'T%LkRaQ2I,4c'0R}Q2DQ0LQ3dPkPa%6aPdQ3zPtO1Rd,4cQ0TPcQ3QP^PdPJQ3zPtPtPtI0MJ0kN91OPCH1MP}Q0DQ3CQ2MQ2;Q3_'1H0WR}$1S%L}Rd#9Q1F$0PQ1FQ1F#PR^Q1FQ1FP^I0YQ0r#PR^PEQ0BQ2OQ2PQ0yQ0`Q4BQ2x%k\Ra+0QQ0R5^I-2LIRkQ2t00UaRa00fIQ0YQ0XQ0W3^Q3lQ0\,Sa22Ek0H1640[Q07PlP=Q4UPFQ2zP>Q2{Q2}7xFK0eQ2QPnPnQ4P=\n7Q42Q1M5\nPxPnQ31PxPnQ2hQ3:'t9cn;PxPnQ2]PxPnQ3jQ3o5\nPxPnQ34PxPnQ36PxPnPnQ37Q2dPxQ3=J0KFGFGFGJ0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEX7eXAeXPeXQeQ3nQ4Q/8281oFQ4RQ0c:0;2FQ18,8Q1<R31<3PQ4[/8UQ41Q1</<V15PVS4[Q1<Q1</5z+0N[[[[[[[\b[[[^0E^2E^4E^5E^?E^BE^FE^7e^Ae^Pe^QeP5Q2@/5z%9sQ2_Q1@,0BQ1EPsQ2fQ2RQ3EQ2@Q1@PDP2Q17PtP:Q1XQ1OQ1dQ1zQ27Q1xOFb6b8bIbNbLbHbObMb<b=b@81~9I0jQ20/5hQ209_h9+00Q1aQ2YPNPtPcQ2LH07P=PGQ3LQ2i:0Owc:0@NNRhQ23';R9/<zXEG%6m10fmRmeS23PmQ1F,BNRb#610wbRbeS1FPb%6p10tpRpeS2iPpQ0rQ2;80Oc:0@NNRtQ0TQ1b+0zRV#LS2L';RU/<zQ2`,4cRQ,;tRk/<zPJQ2>PUPkPJPJPJQ3ZPtPt%6tQ2LPQPJPJQ3xPVPQQ0TPcQ3QQ1bQ2`PJQ3zPwPwPwI0MS2`J0kJ1tN:2RS3xPzPzQ0EL1n1T}V10dQRQQ2DQ0LQ3dP}Pd%6dPVQ3zPwO1Rw,4cQ0TPcQ3QQ1bPwQ2`J0kN91OPFH1MS2`PQQ0DQ3NQ3EQ2jQ2Z'1H0WRw$1SS3N%Lw#9RwQ0r$0PRVQ0rP^Q0rQ0rP^I0YR^Q2yPEQ0BQ2OQ2PQ0yQ3_Q4APuQ3CCzRd00yvR}%9dQ3SQ4@Q3`7qu<1Ev#9\?[R?Q0=Q0XQ4SQ0UQ2u3^40]PIPaQ0=Q3a+0QQ0YQ0XQ0WQ2NQ2u+0UQ4T3^I1NQ2tQ3aQ1yQ0WQ0VQ2uQ3yI1N41e/[0H16Q07PlP=Q4U9xlBP>Q2?P2PlP@Q2|P2Q3HK0eI09Q2QPnQ4GPxPnQ4HPxPnPnP~Q2VPxPnQ0>PxPnQ38PxPnPnQ3<Q39Q2h'i<2^1PxPnQ4VPxPnQ0@PxPnQ0[PxPnQ1~PxQ4ZFGFGI2dFGJ0:FGQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEXaEX7eXAeXPeXQeX`eP2P>PBQ2~H11Q3I,0D10F310@3Q3A:0;R3Q2o=_PzQ1S,8X%9RRX/8ZQ0P,8XQ4[Q1<=_Rz[[[[[[[[[[^0E^2E^4E^5E^?E^BE^FE^aE^7e^Ae^Pe^Qe^`eP5Q3>/5zQ2H/5zQ15#9Q44Q0dQ1X,BNPyQ15P:Q2HQ3>PBQ15Q2H80Oc:0@NNRzPDP2P3PWQ19PoPsQ1WQ1\Q1YOGb6b8bIbNbLbHbObMH0Hb<b=b@Q3wPBEYPGQ3L1BN@Rs/5h1<9s+00XEGQ23PmQ1FPbQ2iPp1BNDRN/5tRt1<UNRp+001<kNRb-00tPtPpPtPb&2AtPJQ2>PUPkQ3xPNPN%6NL1nJ47Q2`PQQ3NPwPVP^Q2yPEQ0BQ2OQ2PQ0yP}P?Q0WQ29Q0R'S+0fR?Q4<Q2uQ0?3^Q2uQ4C'S/[0'[80[?Q07PlPFQ2|P=Q2zP>PlP@PlPDQ4UI20K0eQ2QPnPnPnP7PnQ2<01X;H0|PnPnP;PrQ2<=cnrI0hPxPnPnP;Q0]PxPnPnQ329hnjQ32Q39/i;'~=UnjPxPnPnPAQ32PxPnQ35PxQ3hQ3G,~A=Unj646nH1vJ0:J0DJ0:J0DQ2SQ2Tb9b:b;X0EX2EX4EX5EX?EXBEXFEX7eQ4IQ4L61oFQ4M15=2Q1N/<=+0010B3Q3B15DCQ3A=_CD+00[[[[[^0E^2E^4E^5E^?E^BE^FE^7eP5Q0dPyP:Q2HQ3>PBPzQ3FPDP2PPPWQ1YO=b6b8bIbNbLbHbObMH0Hb<b=b@Q3wPBEYJ45bxWxXS8Q2MQ2;Q1UQ3C'140vQ2=Q3k443N:42J2wJ2wP4Q0bP=Q1rQ2^+1{H2eec0Tc0]Q0CQ0FQ0GP4P<Q0HQ0IQ0JQ0KQ1|Q3YQ3Y/`KQ3YP[Q26P]Q2CI40P_Q3gP`Q3sI1dQ28Q2fQ1EQ3EQ2jQ2ZP6Q0fQ0OQ1uPcQ1EQ2ZP{DwP{n0100000020000Q3YQ28Q2fQ21I0rF}Q3Y#ZI0RP=P>P5N;14&1=>Q09$1=+1]Q1hQ3YPBP@P=Q3YQ3Y60JOQ0o#ZRBQ3YQ3Y40JQ3Y-2=OQ3Y-2=BH2yP>P5O7Y0[Y0QWWWUWVND3~c0gY0OY0NP>P5O2n2001000000121000000W1Y0MP>P5O2n2001000000121000000W1Y0LP>P5O2n2011000000121000000W1Y0KP>P5O2n2011000000121000000W1Y0_P>P5O2n2011000000121000000W1WrP>P5O2n2011000000121104000bqc0Rc0^b_btbybzWyY0pP>P5O2n2001000000121000000W1WzP>P5O2n2001000000121000000bbc0wc0ZbRc0{c0Xc0Yc0jY0`Y0lP>P5O2n2001000000121000000bbY0dY0mP>P5O2n2001000000121000000bbY0UY0kP>P5O2n2001000000121000000bbY0\Y0iP>P5O2n2001000000121000000bbW^W3Q2BP5Q1jQ3UL3}c0Wb{b1c0=b1c0:b1b|b1c0>b1c0<b1c0;b1b~b1b}b1b>b1W{W>P>P5O2n2001000000121000000b>Y0>W>P>P5O2n2001000000121000000b>Y0=W>P>P5O2n2001000000121000000b>Y0<W>P>P5O2n2001000000121000000b>Y0;W>P>P5O2n2001000000121000000b>Y0:W>P>P5O2n2001000000121000000b>W~W>P>P5O2n2001000000121000000b>W}W>P>P5O2n2001000000121000000b>W|W>P>P5O2n2001000000121000000b>Y0sW>P>P5O2n2001000000121000000b>Y0rW>P>P5O2n2001000000121000000b>Y0qW>P>P5O2n2001000000121000000b>W3W>Q1w$0=Q1k92HYPHPYQ0{Q1pP5DrQ0xQ1t00B5b1W3W>n0110201020100P5P=O2b>bJW3WjZ0yEP5O1Q1gQ1g<0i\&1uERB52|Q1g9eHYPHPYQ0{Q1fP5DrQ0xQ1`00B5b1W3Wjn10110701021110100P5P=O2bjbcW3WkZ0zEP5O1Q1XQ1X/C\+0\=2|BQ1X9eHYPHPYQ0{Q1[P5DrQ0xQ1^00B5b1W3Wkn10110701021110100P5P=O2bkbcW3WoZ0~EZ0}MP>P5O2n2001112010121103101P5P=O2boc12W3WhXEEP5O1P|PoQ0^PBCnAeHYoPHPYQ0{Q1KP5DrQ0xQ1L00B5b1W3Whn10110701021110100P5P=O2bhbcW3WiZ14EP5O1P|Q1JQ0_PBCnQ1J9eHYPHPYQ0{Q1IP5DrQ0xQ1?00B5b1W3Win10110701021110100P5P=O2bibcW3WgZ0vEP5O1P|PfP]PBCnAeHYfRfPHPYQ0{Q1GP5DrQ0xQ1H00B5R]b1W3Wgn10110701021110100P5P=O2bgbcW3WfXmEP5O1P|Q0eP[PBCnQ0e9eHYRBPHPYQ0{Q0tP5DrQ0xQ0v00B5R[b1W3R|Wfn10110701021110100P5P=O2bfbcW3Q0:PHPYQ0zXqHRoQ0tP5DrQ0xP[b1X3BWTXRMP>P5O2RBn10110501020120103105WTZ0eEP5O1Q0:Q00PMQ1292HYQ0k]3P5Q1;92HYPHPYQ0{Q12P5DrQ0xQ0k00B5b1W3PBn10110500020020103105WTXEGP5O1g03i6Q0:Q00PMQ0t92HYQ0v]3P5P|Q0:Q119eHYPHPYPo%jqP5DrQ0xPSP4PTPLP4Q11Q0|Q0uQ0sEEPiD@00B5b1W3WTXRMP>P5O2n10110500020020103105WTXJMXbMRqY0GP=P>P5O3R|P|g03ibPqY0GP=P>P5O3RqPqQ0:Q00PMQ0u#jRq92HYPSP4PTPLP4Q0sQ14PiQ0eJ0mPgD@Rg]3RiP5Q0w92HYR|PHPYPoPqP5DrQ0x20Bg5Rgb1W3Q0:PHPYQ0zZ0xHQ1GP5DrQ0xP]b1X3fWTXqMP>P5O2n10110500020020103105WTXRMXEGZ10GZ0H6P@P=P>P5O4Q0:Q00PMPiP5PHPYQ0{PqP5DrQ0xPgb1X3|Q0:PHPYPoQ1GP5DrQ0xP]b1X3fWTXRMP>P5O2n10110500020020103105WTXEGXmEZ0|GZ0H6P@P=P>P5O4n01103010811101101003010G1061023010G1061023010G1061023010G1061024010H1101001034010H10|108100XRMP>P5O2n10110501020021103105P=O1beb1W3WeQ0j$0=P6PHQ08$2BR=PYQ0ln0100000020001Q0m52HPHP6PHP=PYQ0gn0100000020001Q0{Q0hP5DrQ0xQ0i00B5b1W3Wen0110201020101P5PCO2bebJc0fbubuW^W3Y0tY0PY0oY11Y0JY0hY0IY0FY0EPLPSP4PTP<POQ0HQ0IQ0JQ0KQ01Q04P<POP5P>H2WY0EN<3zeY0uY0no"). Qed.

Theorem node_x_sound_XIMemset :
  fill_spec SEGS (x_imemset A) 256 -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XIMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

Theorem node_x_sound_XMemset :
  fill_spec SEGS (x_memset A) two64 -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

Theorem node_x_sound_XIMemcpy :
  copy_spec SEGS (x_imemcpy A) -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XIMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemcpy :
  copy_spec SEGS (x_memcpy A) -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemIsZero :
  miz_spec SEGS (x_memiszero A) -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XMemIsZero.
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.

Theorem node_x_sound_XIStrncpy :
  istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XIStrncpy.
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.

Theorem node_x_sound_XPopFree :
  popfree_spec SEGS (x_popfree A) -> x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XPopFree.
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.

End Sound.
End FPX_1.


End APSX.
End AsanPlanSoundSums.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
Module SegRun.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_SegRun () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List8map_consc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX=nth_repeat_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXDfirstn_skipn_map_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib5Lists7ListDef6firstnC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List7map_extC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List6map_idK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00c69OSSVerify5KrLib7Mh_01306SegRun2SR4wlogC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR4wdenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9mem_denotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26adenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appi69OSSVerify5KrLib7Mh_01306SegRun2SR4went00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun39env_agreeC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24expr08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28expr_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<edenot_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC<expr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3<expr_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00c69OSSVerify5KrLib7Mh_01306SegRun2SR:wl_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffc69OSSVerify5KrLib7Mh_01306SegRun2SR<went_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbk69OSSVerify5KrLib7Mh_01306SegRun2SR4went01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25saddr01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?edenot_agree_APC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25a_offC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR4went02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR4went03C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2InI47Corelib4Init5Peano2le00C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC46Stdlib5Lists4List>forallb_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationC56Stdlib5Arith8PeanoNat3Nat3lebC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init5Peano2ltC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02c69OSSVerify5KrLib7Mh_01306SegRun2SR6closedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26s_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:sr_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=sr_vars_lt_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=kn_vars_lt_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC:kn_vars_ltC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib4Init5Logic7f_equalI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01c69OSSVerify5KrLib7Mh_01306SegRun2SR=some_pair_injC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR:step_blockC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR3INVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S7know_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR9STEP_POSTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR<closed_partsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25carryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27s_cleanC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24s_pcC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List7existsbC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;itab_lookupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29sym_stepXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23clrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2=sym_execTX_goC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01129AxSymRun3;runTX_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S5st_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR:wden_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib?AxSymExec3Sound4AX2S8sc_denotC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib7Mh_01129AxSymRun3;carry_afterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR9wden_wlogC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:sym_execTXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28sidecond00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24itabC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5instr00I69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27stepres00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27scr_nilC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01c69OSSVerify5KrLib7Mh_01306SegRun2SR7ret_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR3regC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_lec69OSSVerify5KrLib7Mh_01306SegRun2SR:reg_sound1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_01126LibSym8u64_of_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula05C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25two64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z8inj_succC59OSSVerify5KrLib?AxSymExec3Sound4AX2S9kentry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;kimg_precutC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minK69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry03C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26kentry0:C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op201I46Stdlib5Lists4List6Exists00I47Corelib7Numbers7BinNums8positive00c69OSSVerify5KrLib7Mh_01306SegRun2SR9step_copyC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28facts_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC6flat_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC;kwritable_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2>ranges_apart_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC:copy_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX29split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23xhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8sr_freshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_updC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc69OSSVerify5KrLib7Mh_01306SegRun2SR:after_callC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC59OSSVerify5KrLib?AxSymExec3Sound4AX2S;facts_of_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S5elenZC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>w_flat_x_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S6estartC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAkwritable_x_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib?AxSymExec3Sound4AX2SDranges_apart_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX@copy_facts_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR=ret_lit_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;reg_sound10C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;reg_sound11C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;reg_sound12C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSXAw_split_lit_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S9xhi_soundC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_modC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8iff_reflc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX7kept_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX8ext_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>ext_call_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR>nth_sr_vars_ltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>split_lit_varsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01128AsanPlan2AP<expr_vars_ltC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX9adenot_SAC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?regs_after_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC8kn_havocC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR>kimg_precut_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX?w_know_ok_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>know_ok_agree'C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC3NCSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC<caller_savedC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib7Mh_01306SegRun2SR9pow64_posC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc69OSSVerify5KrLib7Mh_01306SegRun2SR9step_fillC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC47Corelib4Init5Logic5proj2c69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX<Z_to_bv8_modC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryc69OSSVerify5KrLib7Mh_0130AAsanPlanSoundSums4APSX>wbytes_fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S4flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib5Lists4List=repeat_lengthC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc69OSSVerify5KrLib7Mh_01306SegRun2SR;wslots_wentC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR6wslotsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphc69OSSVerify5KrLib7Mh_01306SegRun2SR:wslots_outC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z7mul_0_rC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24ridxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2:itab_entryC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC46Stdlib5Lists4List9nth_errorc69OSSVerify5KrLib7Mh_01306SegRun2SR;fsd_targetsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01K4ELinuxProcessSemantics5Riscv5Instr5instr02K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?K4ELinuxProcessSemantics5Riscv5Instr5instr0BK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0Jc69OSSVerify5KrLib7Mh_01306SegRun2SR9itab_factC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkAlu_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387FPSteps;fp_step_fsdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4ZdivAZplus_mod_idemp_lK59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0KK4ELinuxProcessSemantics5Riscv5Instr5instr0LK4ELinuxProcessSemantics5Riscv5Instr5instr0MK4ELinuxProcessSemantics5Riscv5Instr5instr0NK4ELinuxProcessSemantics5Riscv5Instr5instr0OK4ELinuxProcessSemantics5Riscv5Instr5instr0PK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0SC47Corelib4Init9Datatypes7nat_indC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26sr_getC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkAluC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr4ffmt02I4ELinuxProcessSemantics5Riscv5Instr4ffmt00I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00c69OSSVerify5KrLib7Mh_01306SegRun2SR;consecutiveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28expr_eqbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapc69OSSVerify5KrLib7Mh_01306SegRun2SR;step_fsdseqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SRBfsd_targets_lengthC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?consecutive_nthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7fsd_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS8ext_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>ext_list_agreeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List6in_seqC59OSSVerify5KrLib=AsanPlanSound3APS;ext_list_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22evC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:map_ext_inC46Stdlib5Lists4List9seq_shiftC46Stdlib5Lists4List8cons_seqc69OSSVerify5KrLib7Mh_01306SegRun2SR@wden_wslots_wentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>regs_ok_agree'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR6kslotsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffc69OSSVerify5KrLib7Mh_01306SegRun2SR;wslots_slotC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List7map_nthc69OSSVerify5KrLib7Mh_01306SegRun2SR<wslots_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR>fld_sources_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2SAkn_readable_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28to_saddrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S>to_saddr_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387FPSteps;fp_step_fldC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX2;kn_readableC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC49OSSVerify5KrLib8PropExec6fp_csrC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib8PropExec7FPState01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c69OSSVerify5KrLib7Mh_01306SegRun2SR;step_fldseqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7fld_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS>env_agree_reflC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX22ebC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0075:AxSymExec33AX23env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS3updC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR5efoldC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26mkAluwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<mkAluw_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC69OSSVerify5KrLib7Mh_0075:AxSymExec33AX24mkMdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S:mkMd_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkMdwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkMdw_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25mkExtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX27ext_valC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6leb_leC59OSSVerify5KrLib?AxSymExec3Sound4AX2S;mkExt_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX28blob_valC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_reflC47Corelib4Init9Datatypes3orbK47Corelib4Init5Logic2or02c69OSSVerify5KrLib7Mh_01306SegRun2SR5evarsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_tranC46Stdlib5Lists4List4inclC46Stdlib5Lists4List>existsb_existsC56Stdlib5Arith8PeanoNat3Nat6eqb_eqK47Corelib4Init5Logic2or01c69OSSVerify5KrLib7Mh_01306SegRun2SR:evars_monoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR4zseqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00c69OSSVerify5KrLib7Mh_01306SegRun2SR:eval_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX26erangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?AxSymExec3Sound4AX2S<erange_soundC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c69OSSVerify5KrLib7Mh_01306SegRun2SR7zseq_InC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8eqb_reflc69OSSVerify5KrLib7Mh_01306SegRun2SR;evars_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;efold_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR5EVMAXC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR<step_evalregC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR@eval_range_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib?AxSymExec3Sound4AX2S:nth_sr_updC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR9join_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APSAexpr_vars_lt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS<env_agree_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS?env_agree_transC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR6arm_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR<step_diamondC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR6acs_ofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC<branch_probeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR<arm_ok_partsC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtC56Stdlib5Arith8PeanoNat3Nat6eq_decC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib9micromega;ZifyClasses9not_morphc69OSSVerify5KrLib7Mh_01306SegRun2SR;ridx_of_natC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?join_regs_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR8ridx_bv5C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206c69OSSVerify5KrLib7Mh_01306SegRun2SR9no_strlenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallc69OSSVerify5KrLib7Mh_01306SegRun2SR8step_reqC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep01C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep04C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep05C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;step_strlenC1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep07C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep08C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep09C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep02C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib7Mh_01306SegRun2SR5sstep03C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR@strlen_step_stmtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR8seg_stepC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR@step_block_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?step_copy_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?step_fill_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SRAstep_fsdseq_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SRAstep_fldseq_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SRBstep_diamond_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SRBstep_evalreg_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7seg_runC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR>seg_step_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01126LibSym4EnvRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01126LibSym<EnvR_regs_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR=seg_run_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075:AxSymExec33AX25sr_idC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR6regionC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7within1C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR<regions_flatC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;went_withinC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib7Mh_01306SegRun2SR=within1_soundC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7kn_wordC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?region_flat_chkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implc69OSSVerify5KrLib7Mh_01306SegRun2SR:regions_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR;run_post_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7post_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR5ps_pcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR:ps_regionsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR8ps_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0075<AsanPlanCore3APC:kentry_eqbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR7ps_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SREregion_flat_chk_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR?regions_ok_flatC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_01306SegRun2SR:wden_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=AsanPlanSound3APS=kentry_eqb_eqC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib7Mh_01306SegRun2SR9post_spec00C1?~~~~~~~~~~~~~~~".
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SR.
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable IT : itab.
Variable x_cpy : Z.      (* [comment removed for export] *)
Variable x_set : Z.      (* [comment removed for export] *)
Variable x_len : Z.      (* [comment removed for export] *)
Variable ro_lo ro_hi : Z. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive went : Type :=
| WSt (a : saddr) (wd : nat) (v : expr)                       (* [comment removed for export] *)
| WCopy (db : expr) (dk : Z) (sb : expr) (sk : Z) (n : Z)     (* [comment removed for export] *)
| WFill (db : expr) (dk : Z) (n : Z) (c : Z).                 (* [comment removed for export] *)

Fixpoint wden (E : env) (M : word -> option byte) (w : list went) : word -> option byte :=
  match w with
  | [] => M
  | WSt a wd v :: r => wbytes (wden E M r) (adenot E a) (word_to_le_bytes wd (edenot E v))
  | WCopy db dk sb sk n :: r =>
      let m := wden E M r in
      match rdn segs m (adenot E (SA sb sk)) (Z.to_nat n) with
      | Some bs => wbytes m (adenot E (SA db dk)) bs
      | None => m
      end
  | WFill db dk n c :: r => wbytes (wden E M r) (adenot E (SA db dk)) (repeat (Z_to_bv 8 c) (Z.to_nat n))
  end.

Fixpoint wlog (log : list sentry) : list went :=
  match log with [] => [] | SE a wd v :: r => WSt a wd v :: wlog r end.

Lemma wden_wlog : forall E M log w, wden E M (wlog log ++ w) = mem_denot E (wden E M w) log.
Proof.
  intros E M log w. induction log as [|[a wd v] r IH]; cbn [wlog app wden mem_denot]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition went_vars_lt (b : nat) (g : went) : bool :=
  match g with
  | WSt a _ v => APC.expr_vars_lt b (a_base a) && APC.expr_vars_lt b v
  | WCopy db _ sb _ _ => APC.expr_vars_lt b db && APC.expr_vars_lt b sb
  | WFill db _ _ _ => APC.expr_vars_lt b db
  end%bool.
Definition wl_vars_lt (b : nat) (w : list went) : bool := forallb (went_vars_lt b) w.

Lemma edenot_agree_AP : forall b E E' e, env_agree b E E' -> APC.expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e Hag H. apply (edenot_agree b); [exact Hag|].
  induction e; cbn in *; try reflexivity; try exact H;
    try (apply andb_true_iff in H as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity).
Qed.

Lemma wden_agree : forall b E E' M w, env_agree b E E' -> wl_vars_lt b w = true -> wden E M w = wden E' M w.
Proof.
  intros b E E' M w Hag. induction w as [|g r IH]; intros H; [reflexivity|].
  cbn [wl_vars_lt forallb] in H. apply andb_true_iff in H as [Hg Hr].
  destruct g as [[ab ak] wd v|db dk sb sk n|db dk n c]; cbn [wden went_vars_lt a_base] in *;
    rewrite (IH Hr).
  - apply andb_true_iff in Hg as [H1 H2]. unfold adenot. cbn [a_base a_off].
    rewrite (edenot_agree_AP b E E' ab Hag H1), (edenot_agree_AP b E E' v Hag H2). reflexivity.
  - apply andb_true_iff in Hg as [H1 H2]. unfold adenot. cbn [a_base a_off].
    rewrite (edenot_agree_AP b E E' db Hag H1), (edenot_agree_AP b E E' sb Hag H2). reflexivity.
  - unfold adenot. cbn [a_base a_off]. rewrite (edenot_agree_AP b E E' db Hag Hg). reflexivity.
Qed.

Lemma wl_vars_lt_mono : forall b b' w, (b <= b')%nat -> wl_vars_lt b w = true -> wl_vars_lt b' w = true.
Proof.
  intros b b' w Hle H. unfold wl_vars_lt in *. rewrite forallb_forall in *. intros g Hg. specialize (H g Hg).
  assert (MONO : forall e, APC.expr_vars_lt b e = true -> APC.expr_vars_lt b' e = true).
  { intros e. induction e; cbn; intros He; try reflexivity; try exact He;
      try (apply andb_true_iff in He as [H1 H2]; rewrite (IHe1 H1), (IHe2 H2); reflexivity);
      try (apply IHe; exact He).
    apply Nat.ltb_lt in He. apply Nat.ltb_lt. lia. }
  destruct g; cbn [went_vars_lt] in *;
    repeat (apply andb_true_iff in H as [?H1 H]); rewrite ?andb_true_iff; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive sstep : Type :=
| SBlock (stops : list Z)
| SCopy
| SFill
| SFsdSeq (n : nat)        (* [comment removed for export] *)
| SFldSeq (n : nat)        (* [comment removed for export] *)
| SStrlen (k : Z)          (* [comment removed for export] *)
| SExpect (pc : Z)
| SDiamond (joinpc : Z)    (* [comment removed for export] *)
| SEvalReg (r : nat).      (* [comment removed for export] *)

Variable BFUEL : nat.

(* [comment removed for export] *)
Definition closed (ss : sym_state) (w : list went) : bool :=
  (APC.sr_vars_lt (s_next ss) (s_regs ss) && APC.kn_vars_lt (s_next ss) (s_know ss) && wl_vars_lt (s_next ss) w
   && match s_log ss with [] => true | _ => false end)%bool.

Definition reg (ss : sym_state) (n : nat) : expr := nth n (s_regs ss) (ELit 0).
Definition ret_lit (ss : sym_state) : option Z :=
  match reg ss 1 with
  | ELit r => if (Z.eqb (r mod 2) 0 && Z.ltb r two64 && Z.leb 0 r)%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition after_call (ss : sym_state) (ret : Z) (rv : expr) (k' : list kentry) : sym_state :=
  let nx := s_next ss in
  SS ret (sr_upd (APC.sr_fresh (s_regs ss) APC.caller_saved nx) 10 rv) [] k' (nx + APC.NCS)%nat.

Definition step_block (stops : list Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let ss' := sym_execTX segs IT 0%nat BFUEL true stops ss in
  match carry (s_log ss') (s_know ss') [] with
  | (kn', [], _) => Some (SS (s_pc ss') (s_regs ss') [] kn' (s_next ss'), wlog (s_log ss') ++ w)
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kimg_precut (k : list kentry) (db : expr) (dk n : Z) : list kentry :=
  match k with
  | [] => []
  | KImg lo hi :: r =>
      match db with
      | ELit 0 =>
          (if Z.ltb lo (Z.min dk hi) then [KImg lo (Z.min dk hi)] else [])
          ++ (if Z.ltb (Z.max lo (dk + n)) hi then [KImg (Z.max lo (dk + n)) hi] else [])
          ++ kimg_precut r db dk n
      | _ => KImg lo hi :: kimg_precut r db dk n
      end
  | K :: r => K :: kimg_precut r db dk n
  end.

Definition step_copy (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in
  if negb (Z.eqb (s_pc ss) x_cpy) then None else
  match ret_lit ss, reg ss 12 with
  | Some ret, ELit n0 =>
      let n := n0 mod two64 in
      let dst := reg ss 10 in let src := reg ss 11 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xhi fk dst, xhi fk src with
      | Some dhi, Some shi =>
      if (Z.ltb 0 n && Z.leb n 2048 && Z.ltb (dhi + n) two64 && Z.ltb (shi + n) two64
          && APC.flat_x fk db dk (ELit n) && APC.flat_x fk sb sk (ELit n)
          && APC.kwritable_x fk k db dk (ELit n) && ranges_apart_x fk db dk (ELit n) sb sk (ELit n))%bool
      then match APC.copy_facts segs (Z.to_nat n) k sb sk db dk n with
           | Some kc =>
               let k' := kc ++ APC.kn_havoc (kimg_precut k db dk n) db dk (ELit n) in
               if APC.kn_vars_lt (s_next ss) k' then Some (after_call ss ret dst k', WCopy db dk sb sk n :: w) else None
           | None => None
           end
      else None
      | _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition step_fill (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in
  if negb (Z.eqb (s_pc ss) x_set) then None else
  match ret_lit ss, reg ss 11, reg ss 12 with
  | Some ret, ELit c0, ELit n0 =>
      let n := n0 mod two64 in let c8 := (c0 mod two64) mod 256 in
      let dst := reg ss 10 in let '(db, dk) := split_lit dst in
      match xhi fk dst with
      | Some dhi =>
      if (Z.ltb 0 n && Z.leb n (2 ^ 40) && Z.ltb (dhi + n) two64
          && APC.flat_x fk db dk (ELit n) && APC.kwritable_x fk k db dk (ELit n))%bool
      then let k' := (if Z.eqb c8 0 then KZero (SA db dk) (ELit n) else KFill (SA db dk) (ELit n) c8)
                      :: APC.kn_havoc (kimg_precut k db dk n) db dk (ELit n) in
           if APC.kn_vars_lt (s_next ss) k' then Some (after_call ss ret dst k', WFill db dk n c8 :: w) else None
      else None
      | None => None
      end
  | _, _, _ => None
  end.


(* [comment removed for export] *)
Fixpoint fsd_targets (p : Z) (n : nat) (ss : sym_state) : option (list (expr * Z)) :=
  match n with
  | O => Some []
  | S n' =>
      match itab_lookup IT p with
      | Some (FStore FMT_D rs1 _ imm) =>
          match fsd_targets (p + 4) n' ss with
          | Some r => Some (split_lit (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) :: r)
          | None => None
          end
      | _ => None
      end
  end.
Fixpoint consecutive (b : expr) (k : Z) (l : list (expr * Z)) : bool :=
  match l with [] => true | (b', k') :: r => expr_eqb b' b && Z.eqb k' k && consecutive b (k + 8) r end%bool.
Fixpoint kslots (db : expr) (dk : Z) (vs : list expr) : list kentry :=
  match vs with [] => [] | v :: r => KWord (SA db dk) 8 v :: kslots db (dk + 8) r end.
Fixpoint wslots_went (db : expr) (dk : Z) (vs : list expr) (acc : list went) : list went :=
  match vs with [] => acc | v :: r => wslots_went db (dk + 8) r (WSt (SA db dk) 8 v :: acc) end.
Definition step_fsdseq (n : nat) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  match fsd_targets (s_pc ss) n ss with
  | Some ((db, dk) :: rest) =>
      let len := 8 * Z.of_nat n in
      match xhi fk (mkAlu ALU_ADD db (ELit dk)) with
      | Some dhi =>
      if (consecutive db (dk + 8) rest && Z.ltb (dhi + len) two64
          && APC.flat_x fk db dk (ELit len) && APC.kwritable_x fk k db dk (ELit len) && APC.expr_vars_lt nx db)%bool
      then let vs := map (fun j => EVar (nx + j)%nat) (seq 0 n) in
           let kh := APC.kn_havoc (kimg_precut k db dk len) db dk (ELit len) in
           let k' := kslots db dk vs ++ kh in
           if (APC.kn_vars_lt (nx + n) k' && APC.kn_vars_lt nx kh)%bool
           then Some (SS (s_pc ss + 4 * Z.of_nat n) (s_regs ss) [] k' (nx + n)%nat, wslots_went db dk vs w)
           else None
      else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint fld_sources_ok (p : Z) (n : nat) (ss : sym_state) : bool :=
  match n with
  | O => true
  | S n' =>
      match itab_lookup IT p with
      | Some (FLoad FMT_D _ rs1 imm) =>
          let a := to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm) in
          kn_readable segs (facts_of (s_know ss)) (s_know ss) (a_base a) (a_off a) 8 && fld_sources_ok (p + 4) n' ss
      | _ => false
      end
  end%bool.
Definition step_fldseq (n : nat) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  if fld_sources_ok (s_pc ss) n ss
  then Some (SS (s_pc ss + 4 * Z.of_nat n) (s_regs ss) [] (s_know ss) (s_next ss), w)
  else None.


(* [comment removed for export] *)
Fixpoint bytes_nonzero (fk k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match know_lookup segs k b off 1 false [] [] with
            | LHit (ELit z) [] _ => negb (Z.eqb (z mod 256) 0) && bytes_nonzero fk k b (off + 1) n'
            | _ => false
            end
  end%bool.
Definition byte_zero (k : list kentry) (b : expr) (off : Z) : bool :=
  match know_lookup segs k b off 1 false [] [] with LHit (ELit z) [] _ => Z.eqb (z mod 256) 0 | _ => false end.
Fixpoint words_readable (fk k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => kn_readable segs fk k b off 1 && words_readable fk k b (off + 1) n'
  end%bool.
Definition ro_covered (k : list kentry) : bool :=
  existsb (fun K => match K with KImg lo hi => (Z.leb lo ro_lo && Z.leb ro_hi hi)%bool | _ => false end) k.
Definition step_strlen (kz : Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let fk := facts_of k in let nx := s_next ss in
  if negb (Z.eqb (s_pc ss) x_len) then None else
  match ret_lit ss with
  | Some ret =>
      let sp := reg ss 10 in let '(sb, sk) := split_lit sp in
      match xhi fk sp, ealign k sb with
      | Some shi, al =>
          (* [comment removed for export] *)
          let hi := (sk + kz) - (sk + kz) mod 8 + 8 in
          if (Z.leb 0 kz && Z.ltb (shi + (hi - sk)) two64 && Z.leb 3 al
              && bytes_nonzero fk k sb sk (Z.to_nat kz) && byte_zero k sb (sk + kz)
              && words_readable fk k sb (sk + kz + 1) (Z.to_nat (hi - (sk + kz + 1)))
              && APC.flat_x fk sb sk (ELit (hi - sk))
              && ro_covered k)%bool
          then Some (SS ret (sr_upd (APC.sr_fresh (s_regs ss) [11; 12; 13; 14; 15; 16]%nat nx) 10 (ELit kz)) [] k (nx + 6)%nat, w)
          else None
      | None, _ => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition EVMAX : Z := 8192.
(* [comment removed for export] *)
Fixpoint evars (e : expr) (acc : option (list nat)) : option (list nat) :=
  match acc with
  | None => None
  | Some l =>
      match e with
      | ELit _ => acc
      | EVar n => Some (if existsb (Nat.eqb n) l then l else n :: l)
      | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars b (evars a acc)
      | EExt _ _ _ a => evars a acc
      | EBlob _ _ _ _ => None
      end
  end.
(* [comment removed for export] *)
Fixpoint efold (x : nat) (k : Z) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar n => if Nat.eqb n x then ELit k else e
  | EAlu op a b => mkAlu op (efold x k a) (efold x k b)
  | EAluw op a b => mkAluw op (efold x k a) (efold x k b)
  | EMd op a b => mkMd op (efold x k a) (efold x k b)
  | EMdw op a b => mkMdw op (efold x k a) (efold x k b)
  | EExt sx lo n a => if Nat.leb n 8 then mkExt sx lo n (efold x k a) else EExt sx lo n (efold x k a)
  | EBlob _ _ _ _ => e
  end.
Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Definition eval_range (k : list kentry) (e : expr) : option Z :=
  match evars e (Some []) with
  | Some [x] =>
      match erange k (EVar x) with
      | Some (lo, hi) =>
          if (Z.leb lo hi && Z.leb (hi - lo) EVMAX)%bool then
            match efold x lo e with
            | ELit c => if forallb (fun v => expr_eqb (efold x v e) (ELit c)) (zseq lo (Z.to_nat (hi - lo + 1))) then Some c else None
            | _ => None
            end
          else None
      | None => None
      end
  | _ => None
  end.
Definition step_evalreg (r : nat) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  if (Nat.ltb 0 r && Nat.ltb r 32)%bool then
    match eval_range (s_know ss) (reg ss r) with
    | Some c => Some (SS (s_pc ss) (sr_upd (s_regs ss) r (ELit c)) [] (s_know ss) (s_next ss), w)
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition acs_of (ss : sym_state) : APC.acs := APC.ACS ss [] 0 0 0 [] [] 0 (ELit 0) APC.FdStd false.
Fixpoint join_regs (i : nat) (ra rb : list expr) (nx : nat) : list expr * nat :=
  match ra, rb with
  | a :: ra', b :: rb' =>
      if expr_eqb a b then let '(r, n) := join_regs (S i) ra' rb' nx in (a :: r, n)
      else let '(r, n) := join_regs (S i) ra' rb' (S nx) in (EVar nx :: r, n)
  | _, _ => ([], nx)
  end.
Definition arm_ok (joinpc : Z) (nx : nat) (sa : sym_state) : bool :=
  (Z.eqb (s_pc sa) joinpc && match s_log sa with [] => true | _ => false end && Nat.eqb (s_next sa) nx
   && APC.sr_vars_lt nx (s_regs sa) && Nat.eqb (length (s_regs sa)) 32
   && match s_regs sa with ELit 0 :: _ => true | _ => false end)%bool.
Definition step_diamond (joinpc : Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  let k := s_know ss in let nx := s_next ss in
  match APC.branch_probe IT (acs_of ss) with
  | Some e =>
      match erange k e with
      | Some (lo, hi) =>
          let sa := sym_execTX segs IT 0%nat BFUEL true [joinpc] (SS (s_pc ss) (s_regs ss) [] (KRange e lo 0 :: k) nx) in
          let sb := sym_execTX segs IT 0%nat BFUEL true [joinpc] (SS (s_pc ss) (s_regs ss) [] (KRange e 1 hi :: k) nx) in
          if (AxSymRun3.expr_vars_lt nx e && arm_ok joinpc nx sa && arm_ok joinpc nx sb)%bool then
            let '(rj, nx') := join_regs 0 (s_regs sa) (s_regs sb) nx in
            Some (SS joinpc rj [] k nx', w)
          else None
      | None => None
      end
  | None => None
  end.

Definition seg_step (st : sstep) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  if negb (closed ss w) then None else
  match st with
  | SBlock stops => step_block stops ss w
  | SCopy => step_copy ss w
  | SFill => step_fill ss w
  | SFsdSeq n => step_fsdseq n ss w
  | SFldSeq n => step_fldseq n ss w
  | SStrlen kz => step_strlen kz ss w
  | SExpect pc => if Z.eqb (s_pc ss) pc then Some (ss, w) else None
  | SDiamond jp => step_diamond jp ss w
  | SEvalReg r => step_evalreg r ss w
  end.

Fixpoint seg_run (steps : list sstep) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  match steps with
  | [] => if closed ss w then Some (ss, w) else None
  | st :: rest => match seg_step st ss w with Some (ss', w') => seg_run rest ss' w' | None => None end
  end.

(* [comment removed for export] *)
Fixpoint seg_run_dbg (i : nat) (steps : list sstep) (ss : sym_state) (w : list went) : nat * bool * sym_state * nat :=
  match steps with
  | [] => (i, closed ss w, ss, length w)
  | st :: rest => match seg_step st ss w with
                  | Some (ss', w') => seg_run_dbg (S i) rest ss' w'
                  | None => (i, false, ss, length w)
                  end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis IT_ok : itab_sound segs IT.
(* [comment removed for export] *)
Hypothesis COPY : forall fx : FPState, @APSX.copy_spec fx segs x_cpy.
Hypothesis FILL : forall fx : FPState, @APSX.fill_spec fx segs x_set two64.

(* [comment removed for export] *)
Definition strlen_spec (entry : Z) : Prop :=
  forall (fx : FPState) (mem : word -> option byte) (s : word) (buf : list byte) (K : Z)
         (rom : word -> option byte) (regs : bvmap 5 word) (ret : word),
    rdn segs mem s (length buf) = Some buf ->
    (bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf) ->
    bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64 ->
    0 <= K ->
    bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0 ->
    (forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0) ->
    (forall i, ro_lo <= i < ro_hi -> mem (Z_to_bv 64 i) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = s ->
    exists regs',
      msteps segs (@mkst fx regs (Z_to_bv 64 entry) mem rom) (@mkst fx regs' ret mem rom)
      /\ (forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv ->
            getr regs' r = getr regs r)
      /\ getr regs' 10%bv = Z_to_bv 64 K.
(* [comment removed for export] *)

Lemma pow64_pos : (0 < 2 ^ 64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_SegRun ()) ["WithSegs"] "p;2p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8p1002Ip4p7210p10035p4p710R0p8p1003Sp4p710R1P0p8p1003np6061000R2p1005=p4p7210R3p8P2p1005Yp4p710R4p8P2P0p8P2P1p8P2p10065p4p7210R2p8p1006Rp6061000R1p1007cp4p710p8P1P4p8P1P0p8p1008Bp6061000R1P3p8P1p1009Zp4p710R3p8P1P4p8P1p100:6p4p710p8P1p100:Tp4p710p8P1p100;3R4p4p710p8P1P4p4p7210p8P1P0p8P1p100;Pp4p710p8P1p100<0p4p73110R4p8P1p100<Lp4p7210p8P1p100<hp4p710R1p8P2P0p8p100=Gp4p710P0p8P4P0p8P1P3p8P1P0p8g00C]j20Tg01KPg01L6'0o"). Qed.

Definition INV (E : env) (ss : sym_state) (w : list went) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  regs_ok E (s_regs ss) R /\ know_ok segs E (wden E M w) (s_know ss).

Lemma closed_parts : forall ss w, closed ss w = true ->
  AxSymRun3.sr_vars_lt (s_next ss) (s_regs ss) = true /\ AxSymRun3.kn_vars_lt (s_next ss) (s_know ss) = true
  /\ wl_vars_lt (s_next ss) w = true /\ s_log ss = [].
Proof.
  intros ss w H. unfold closed in H.
  apply andb_true_iff in H as [H Hl]. apply andb_true_iff in H as [H Hw]. apply andb_true_iff in H as [Hs Hk].
  rewrite APS.sr_vars_lt_eq in Hs. rewrite APS.kn_vars_lt_eq in Hk.
  repeat split; try assumption. destruct (s_log ss); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition STEP_POST (fx : FPState) (ss : sym_state) (w : list went) (ss' : sym_state) (w' : list went)
           (E : env) (R : bvmap 5 word) (M rom : word -> option byte) : Prop :=
  exists (fx' : FPState) E' R', env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV E' ss' w' R' M /\
    msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) (wden E M w) rom)
                (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (wden E' M w') rom).

Lemma some_pair_inj : forall {A B} (a c : A) (b d : B), Some (a, b) = Some (c, d) -> a = c /\ b = d.
Proof.
ltac2:(KReplay.run1 (kr_t_SegRun ()) ["WithSegs"] "p'0h01Hh12H0h21ai001ah31bi011bh41eh51Ah61Bh71ch81di021oi031pp;2p;1p;4p;3p;6p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8p1002Ip4p7210g0035R0p4p710R1p8p1003Sp4p710R2P1p8p1003np6061000R3p1005=p4p7210R4p8P3p1005Yp4p710R5p8P3P1p8P3P2p8P3p10065p4p7210R3p8p1006Rp6061000R2p1007cp4p710p8P2P5p8P2P1p8p1008Bp6061000R2P4p8P2p1009Zp4p710R4p8P2P5p8P2g01];R5p4p710R6p8P2p100:Tp4p710p8P2p100;3R7p4p710p8P2P7p4p7210p8P2P1p8P2p100;Pp4p710p8P2p100<0p4p73110R7p8P2p100<Lp4p7210p8P2p100<hp4p710R2p8P3P1p8p200R3P6p8P3P5p4p7210R8p8P3P1p8p201R9P6p8P9P8p8P9P1p8p100=Gp4p710P1p8P7P1p8P2P4p8P2P1p8g01]XR1j23Tg00?HR2j14Tg01^8j42Tg01^Xj21Tg00CCj30TP5j68Tg00cEj27Tg00C]j25Tg01ALj49TP0j66Tf1R0f2R5f3R4f5R7f4R8'3R6#4P7P8P4P0C2,16P7P8P5f0R:C2,1630f6R6/37R;#4R<P7P2f7R=/36R>P=P:P1f8R?P=P?P:P:n2001103000120100101P4n10110200021010300X4<P6P7P8P5C2,1;P6P7P4P0C2,1;P:E8A0750%4>R;P=P213?=f9R2P:P1P2P?f:R1P:P0n2001103000120100101P6n10110200021010300X4;P=P6P7P4C2,1>P=P6P8P5C2,1>P0E8A0=78A0?67P2P6A0267f;R>?00?A01=6'7[X22A0?78P2P7A0>??A01:6'7X32A01==A0277151=1527C9P6P:E6W0P=P:E6W0P:O1b1P:O1b1W0W8X35W7W2X69X53o"). Qed.
Lemma step_block_sound : forall (fx : FPState) stops ss w ss' w' E R M rom,
  closed ss w = true -> step_block stops ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M rom.
Proof.
  intros fx stops ss w ss' w' E R M rom Hcl H [HR HK].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_block in H.
  destruct ss as [p sr log k nx rsv]. cbn [s_pc s_regs s_log s_know s_next] in *. subst log.
  set (ss1 := sym_execTX segs IT 0%nat BFUEL true stops (SSR p sr [] k nx rsv)) in H.
  destruct (carry (s_log ss1) (s_know ss1) []) as [[kn' scs] hs] eqn:Hc.
  destruct scs; [|discriminate]. injection H as <- <-.
  assert (Hx : sym_execTX segs IT 0%nat BFUEL true stops (SS p sr [] k nx) = ss1).
  { subst ss1. unfold sym_execTX. reflexivity. }
  pose proof (@runTX_sound fx segs IT 0%nat BFUEL stops p sr k nx E (wden E M w) rom R IT_ok HR HK Fsr Fkn) as X.
  cbn zeta in X. rewrite Hx in X. destruct X as (E' & R' & Hag & Hle & HR' & Hlf & HK' & Hms & _).
  exists fx, E', R'. split; [exact Hag|]. split; [exact Hle|].
  assert (Hw : wden E' M w = wden E M w) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  split.
  - split; cbn [s_regs s_know]; [exact HR'|].
    rewrite wden_wlog, Hw. eapply carry_after; [exact Hc | exact Hlf | exact HK' | constructor].
  - cbn [s_pc]. rewrite wden_wlog, Hw. exact Hms.
Qed.

(* [comment removed for export] *)
Lemma reg_sound1 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 1%bv = edenot E (reg ss 1).
Proof.
ltac2:(KReplay.run1 (kr_t_SegRun ()) ["WithSegs"] "h01Eh12HRh21Rh32ssp;1p;2p;3p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8g002IR0p4p7210p10035p4p710R1p8p1003Sp4p710R2P1p8p1003np6061000R3p1005=p4p7210R4p8P3p1005Yp4p710R5p8P3P1p8P3P2p8P3p10065p4p7210R3p8p1006Rp6061000R2p1007cp4p710p8P2P5p8P2P1p8p1008Bp6061000R2P4p8P2p1009Zp4p710R4p8P2P5p8P2p100:6p4p710R5p8P2p100:Tp4p710p8P2p100;3R6p4p710p8P2P6p4p7210p8P2P1p8P2p100;Pp4p710p8P2p100<0p4p73110R6p8P2p100<Lp4p7210p8P2p100<hp4p710R2p8P3P1p8p101_:R3p6061001R7P5p8P7p101];p4p7210R8p8P7P1p8P3p60621000R3P5p8P3P8p8P3P1p8p100=Gp4p710P1p8P6P1p8P2P4p8P2P1p8g00=bj10Tg01;mj18Tg00>Gj11Tg00>ej12TP0j27Tg01O\j16Tg01b9j34Tg02BVj13Tg02C4j35Tg00L>g01Z_g00M?R0#0R1#8#1R2%01#0#0#0#0#1#2'7f2f1#6f0R134P1%30g01\_552O1W1W2W3W0o"). Qed.
Lemma reg_sound10 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 10%bv = edenot E (reg ss 10).
Proof.
ltac2:(KReplay.run1 (kr_t_SegRun ()) ["WithSegs"] "h01Eh12HRh21Rh32ssp;1p;2p;3p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8g002IR0p4p7210p10035p4p710R1p8p1003Sp4p710R2P1p8p1003np6061000R3p1005=p4p7210R4p8P3p1005Yp4p710R5p8P3P1p8P3P2p8P3p10065p4p7210R3p8p1006Rp6061000R2p1007cp4p710p8P2P5p8P2P1p8p1008Bp6061000R2P4p8P2p1009Zp4p710R4p8P2P5p8P2p100:6p4p710R5p8P2p100:Tp4p710p8P2p100;3R6p4p710p8P2P6p4p7210p8P2P1p8P2p100;Pp4p710p8P2p100<0p4p73110R6p8P2p100<Lp4p7210p8P2p100<hp4p710R2p8P3P1p8p101_:R3p6061001R7P5p8P7p101];p4p7210R8p8P7P1p8P3p60621000R3P5p8P3P8p8P3P1p8p100=Gp4p710P1p8P6P1p8P2P4p8P2P1p8g00=bj10Tg01;mj18Tg00>Gj11Tg00>ej12TP0j27Tg01O\j16Tg01b9j34Tg02BVj13Tg02C4j35Tg00L>g01Z_g00M?#0R0#8R1#1R2%00#0#0#0#0#1#2'7f2f1#6f0R034P0%01#3g01\_552O1W1W2W3W0o"). Qed.
Lemma reg_sound11 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 11%bv = edenot E (reg ss 11).
Proof.
ltac2:(KReplay.run1 (kr_t_SegRun ()) ["WithSegs"] "h01Eh12HRh21Rh32ssp;1p;2p;3p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8g002IR0p4p7210p10035p4p710R1p8p1003Sp4p710R2P1p8p1003np6061000R3p1005=p4p7210R4p8P3p1005Yp4p710R5p8P3P1p8P3P2p8P3p10065p4p7210R3p8p1006Rp6061000R2p1007cp4p710p8P2P5p8P2P1p8p1008Bp6061000R2P4p8P2p1009Zp4p710R4p8P2P5p8P2p100:6p4p710R5p8P2p100:Tp4p710p8P2p100;3R6p4p710p8P2P6p4p7210p8P2P1p8P2p100;Pp4p710p8P2p100<0p4p73110R6p8P2p100<Lp4p7210p8P2p100<hp4p710R2p8P3P1p8p101_:R3p6061001R7P5p8P7p101];p4p7210R8p8P7P1p8P3p60621000R3P5p8P3P8p8P3P1p8p100=Gp4p710P1p8P6P1p8P2P4p8P2P1p8g00=bj10Tg01;mj12Tg00>Gj11Tg00>ej13TP0j28Tg01O\j17Tg01b9j36Tg02BVj14Tg02C4j35Tg00L>g01Z_g00M?#0R0#2R1#1R2%00#0#0#0#0#1#3'8f2f1#7f0R036P0%21#4g01\_552O1W1W2W3W0o"). Qed.
Lemma reg_sound12 : forall E ss R, regs_ok E (s_regs ss) R -> getr R 12%bv = edenot E (reg ss 12).
Proof.
ltac2:(KReplay.run1 (kr_t_SegRun ()) ["WithSegs"] "h01Eh12HRh21Rh32ssp;1p;2p;3p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8g002IR0p4p7210p10035p4p710R1p8p1003Sp4p710R2P1p8p1003np6061000R3p1005=p4p7210R4p8P3p1005Yp4p710R5p8P3P1p8P3P2p8P3p10065p4p7210R3p8p1006Rp6061000R2p1007cp4p710p8P2P5p8P2P1p8p1008Bp6061000R2P4p8P2p1009Zp4p710R4p8P2P5p8P2p100:6p4p710R5p8P2p100:Tp4p710p8P2p100;3R6p4p710p8P2P6p4p7210p8P2P1p8P2p100;Pp4p710p8P2p100<0p4p73110R6p8P2p100<Lp4p7210p8P2p100<hp4p710R2p8P3P1p8p101_:R3p6061001R7P5p8P7p101];p4p7210R8p8P7P1p8P3p60621000R3P5p8P3P8p8P3P1p8p100=Gp4p710P1p8P6P1p8P2P4p8P2P1p8g00=bj10Tg01;mj12Tg00>Gj11Tg00>ej13TP0j28Tg01O\j17Tg01b9j36Tg02BVj14Tg02C4j35Tg00L>g01Z_g00M?R0#0R1#2#1R2%01#0#0#0#0#1#3'8f2f1#7f0R136P1%20#0#0#4g01\_552O1W1W2W3W0o"). Qed.

Lemma ret_lit_sound : forall E ss R r, regs_ok E (s_regs ss) R -> ret_lit ss = Some r ->
  getr R 1%bv = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64.
Proof.
  intros E ss R r HR H. unfold ret_lit in H.
  destruct (reg ss 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (reg_sound1 E ss R HR) as R1. rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_of_Z by (unfold two64 in Hlt; lia). exact He.
Qed.

Lemma nth_sr_vars_lt : forall b sr r, APC.sr_vars_lt b sr = true -> (r < 32)%nat -> APC.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [APC.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma kimg_precut_ok : forall E M k db dk n, know_ok segs E M k -> know_ok segs E M (kimg_precut k db dk n).
Proof.
  intros E M k db dk n H. induction k as [|K r IH]; [constructor|].
  apply Forall_cons_iff in H as [HK Hr]. specialize (IH Hr). cbn [kimg_precut].
  assert (PIECE : forall lo hi lo' hi', kentry_ok segs E M (KImg lo hi) -> lo <= lo' -> hi' <= hi ->
                   kentry_ok segs E M (KImg lo' hi')).
  { intros lo hi lo' hi' X Hlo Hhi. cbn [kentry_ok] in *. destruct X as (X0 & X1 & X2).
    split; [lia|]. split; [lia|]. intros i Hi. apply X2. lia. }
  destruct K as [| | |lo hi| | | | | |]; try (constructor; assumption).
  destruct db as [z| | | | | | |]; [destruct z|..]; try (constructor; assumption).
  apply Forall_app. split; [|apply Forall_app; split; [|exact IH]].
  - destruct (Z.ltb lo (Z.min dk hi)) eqn:C; [|constructor]. apply Z.ltb_lt in C.
    constructor; [|constructor]. eapply PIECE; [exact HK | lia | lia].
  - destruct (Z.ltb (Z.max lo (dk + n)) hi) eqn:C; [|constructor]. apply Z.ltb_lt in C.
    constructor; [|constructor]. eapply PIECE; [exact HK | lia | lia].
Qed.

Lemma step_copy_sound : forall (fx : FPState) ss w ss' w' E R M,
  closed ss w = true -> step_copy ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_copy in H.
  destruct (Z.eqb (s_pc ss) x_cpy) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (reg ss 10)) as [db dk] eqn:Hsd. destruct (split_lit (reg ss 11)) as [sb sk] eqn:Hss.
  destruct (xhi (facts_of (s_know ss)) (reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (facts_of (s_know ss)) (reg ss 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  destruct (APC.copy_facts segs (Z.to_nat (n0 mod two64)) (s_know ss) sb sk db dk (n0 mod two64)) as [kc|] eqn:Hcf; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <- <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hap. rename X0 into Hwr. rename X1 into Hfs. rename X2 into Hfd. rename X3 into Hshi'. rename X4 into Hdhi'. rename X5 into Hn2048.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn2048. apply Z.ltb_lt in Hdhi'. apply Z.ltb_lt in Hshi'.
  set (n := (n0 mod two64)%Z) in *. set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64, Hdhi', Hshi'.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; unfold two64 in Hn64; lia).
  destruct (APSX.w_flat_x_sound segs E m fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.w_flat_x_sound segs E m fk sb sk (ELit n) HKf Hfs) as (Slo & Shi & _).
  destruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  pose proof (ranges_apart_x_sound segs E m fk db dk (ELit n) sb sk (ELit n) HKf Hap) as Hapart.
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi, Shi.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  destruct (APSX.copy_facts_sound segs E m k sb db (Z.to_nat n) sk dk n kc HK Hcf ltac:(lia) ltac:(lia) Slo Shi Dlo Dhi)
    as (bs & Hlbs & Hrd & Hkc).
  (* [comment removed for export] *)
  destruct (ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (reg_sound10 E ss R HR) as R10. pose proof (reg_sound11 E ss R HR) as R11.
  pose proof (reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in R10. rewrite (APSX.w_split_lit_denot E (reg ss 11) sb sk Hss) in R11.
  change (bv_unsigned (edenot E db) + dk)%Z with D in R10. change (bv_unsigned (edenot E sb) + sk)%Z with S in R11.
  pose proof (xhi_sound segs E m fk (reg ss 10) dhi HKf Hdhi) as XD. pose proof (xhi_sound segs E m fk (reg ss 11) shi HKf Hshi) as XS.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in XD. rewrite (APSX.w_split_lit_denot E (reg ss 11) sb sk Hss) in XS.
  change (bv_unsigned (edenot E db) + dk)%Z with D in XD. change (bv_unsigned (edenot E sb) + sk)%Z with S in XS.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hc; lia).
  assert (HS64 : 0 <= S < 2 ^ 64) by (clear - Slo Shi Hc; lia).
  rewrite u64_of_Z in XD by exact HD64. rewrite u64_of_Z in XS by exact HS64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by (pose proof pow64_pos; lia). reflexivity. }
  (* [comment removed for export] *)
  assert (A1 : 0 <= n) by (clear - Hc; lia).
  assert (A3 : rdn segs m (Z_to_bv 64 S) (length bs) = Some bs) by (rewrite Hlbs; exact Hrd).
  assert (A4 : store_ok segs m (Z_to_bv 64 D) (length bs) = true) by (rewrite Hlbs; apply Wst; clear - Hc; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 D) + n <= bv_unsigned (Z_to_bv 64 S) \/ bv_unsigned (Z_to_bv 64 S) + n <= bv_unsigned (Z_to_bv 64 D))
    by (rewrite (u64_of_Z D HD64), (u64_of_Z S HS64); exact Hapart).
  assert (A6 : bv_unsigned (Z_to_bv 64 S) + n < 2 ^ 64) by (rewrite (u64_of_Z S HS64); clear - XS Hshi'; lia).
  assert (A7 : bv_unsigned (Z_to_bv 64 D) + n < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi'; lia).
  destruct (COPY fx m (Z_to_bv 64 D) (Z_to_bv 64 S) n bs R (Z_to_bv 64 ret) A1 Hlbs A3 A4 A5 A6 A7 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  (* [comment removed for export] *)
  set (nx := s_next ss) in *.
  exists fx, (APSX.ext_call E nx regs'), regs'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|]. split; [cbn [after_call s_next]; lia|].
  assert (Hw : wden (APSX.ext_call E nx regs') M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (Fdst : APC.expr_vars_lt nx (reg ss 10) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  assert (Fsrc : APC.expr_vars_lt nx (reg ss 11) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb. pose proof (APSX.split_lit_vars _ _ _ _ Hss Fsrc) as Fsb.
  assert (ED : adenot (APSX.ext_call E nx regs') (SA db dk) = Z_to_bv 64 D).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
  assert (ES : adenot (APSX.ext_call E nx regs') (SA sb sk) = Z_to_bv 64 S).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ sb Hag Fsb). reflexivity. }
  assert (MEM : wden (APSX.ext_call E nx regs') M (WCopy db dk sb sk n :: w) = wbytes m (Z_to_bv 64 D) bs).
  { cbn [wden]. rewrite Hw, ES, ED. fold S in Hrd. rewrite Hrd. reflexivity. }
  split.
  - split.
    + cbn [after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd). reflexivity.
    + cbn [after_call s_know]. rewrite MEM.
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      apply Forall_app. split.
      * apply Hkc. rewrite <- Hlbs. apply rdn_wbytes_hit. rewrite u64_of_Z by lia. rewrite Hlbs. lia.
      * eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wbytes_grows].
        intros x Hx. rewrite Hlen in Hx. apply wbytes_out; rewrite ?Hlbs, ?u64_of_Z by lia; lia.
  - cbn [after_call s_pc]. rewrite MEM. rewrite Hpc. exact Hms.
Qed.

Lemma step_fill_sound : forall (fx : FPState) ss w ss' w' E R M,
  closed ss w = true -> step_fill ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_fill in H.
  destruct (Z.eqb (s_pc ss) x_set) eqn:Hpc; [|discriminate]. cbn [negb] in H. apply Z.eqb_eq in Hpc.
  destruct (ret_lit ss) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg ss 11) as [c0| | | | | | |] eqn:H11; try discriminate.
  destruct (reg ss 12) as [n0| | | | | | |] eqn:H12; try discriminate.
  destruct (split_lit (reg ss 10)) as [db dk] eqn:Hsd.
  destruct (xhi (facts_of (s_know ss)) (reg ss 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  injection H as <- <-.
  repeat (apply andb_true_iff in Hc as [Hc ?X]).
  rename X into Hwr. rename X0 into Hfd. rename X1 into Hdhi'. rename X2 into Hn40.
  apply Z.ltb_lt in Hc. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hdhi'.
  set (n := (n0 mod two64)%Z) in *. set (c8 := ((c0 mod two64) mod 256)%Z) in *.
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *.
  assert (Hn64 : 0 <= n < two64) by (subst n; unfold two64; apply Z.mod_pos_bound; lia).
  assert (Hndef : n = (n0 mod two64)%Z) by reflexivity. clearbody n. unfold two64 in Hn64, Hdhi'.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen : elenZ E (ELit n) = n) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  destruct (APSX.w_flat_x_sound segs E m fk db dk (ELit n) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit n) HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E (ELit n))) with (elenZ E (ELit n)) in Dhi.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E ss R ret HR Hret) as (R1 & Hrok & Hret64).
  pose proof (reg_sound10 E ss R HR) as R10. pose proof (reg_sound11 E ss R HR) as R11.
  pose proof (reg_sound12 E ss R HR) as R12. rewrite H12 in R12. cbn [edenot] in R12. rewrite H11 in R11. cbn [edenot] in R11.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in R10. change (bv_unsigned (edenot E db) + dk)%Z with D in R10.
  pose proof (xhi_sound segs E m fk (reg ss 10) dhi HKf Hdhi) as XD.
  rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd) in XD. change (bv_unsigned (edenot E db) + dk)%Z with D in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hc; lia).
  rewrite u64_of_Z in XD by exact HD64.
  assert (R12' : getr R 12%bv = Z_to_bv 64 n).
  { rewrite R12. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Hndef. unfold two64, bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_mod by (pose proof pow64_pos; lia). reflexivity. }
  assert (A1 : 0 <= n) by (clear - Hc; lia).
  assert (A2 : bv_unsigned (Z_to_bv 64 D) + n < 2 ^ 64) by (rewrite (u64_of_Z D HD64); clear - XD Hdhi'; lia).
  assert (A4 : store_ok segs m (Z_to_bv 64 D) (Z.to_nat n) = true) by (apply Wst; clear - Hc; lia).
  assert (A5 : bv_unsigned (Z_to_bv 64 c0) < two64) by (unfold two64; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 c0)) as X; exact (proj2 X)).
  destruct (FILL fx m (Z_to_bv 64 D) (Z_to_bv 64 c0) n R (Z_to_bv 64 ret) A1 A2 A4 A5 Hrok R1 R10 R11 R12')
    as (regs' & Hms & Hkept & Ha0).
  assert (Hc8 : Z_to_bv 8 (bv_unsigned (Z_to_bv 64 c0)) = Z_to_bv 8 c8).
  { subst c8. rewrite APSX.Z_to_bv8_mod. f_equal; try (rewrite Z_to_bv_unsigned; reflexivity). }
  rewrite Hc8 in Hms.
  set (nx := s_next ss) in *.
  exists fx, (APSX.ext_call E nx regs'), regs'.
  pose proof (APSX.ext_call_agree E nx regs') as Hag.
  split; [exact Hag|]. split; [cbn [after_call s_next]; lia|].
  assert (Hw : wden (APSX.ext_call E nx regs') M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (Fdst : APC.expr_vars_lt nx (reg ss 10) = true) by (unfold reg; apply nth_sr_vars_lt; [exact Fsr0 | lia]).
  pose proof (APSX.split_lit_vars _ _ _ _ Hsd Fdst) as Fdb.
  assert (ED : adenot (APSX.ext_call E nx regs') (SA db dk) = Z_to_bv 64 D).
  { rewrite APSX.adenot_SA. f_equal. unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E _ db Hag Fdb). reflexivity. }
  set (M' := wbytes m (Z_to_bv 64 D) (repeat (Z_to_bv 8 c8) (Z.to_nat n))).
  assert (MEM : wden (APSX.ext_call E nx regs') M (WFill db dk n c8 :: w) = M').
  { cbn [wden]. rewrite Hw, ED. reflexivity. }
  assert (FILLED : forall i, 0 <= i < n -> M' (Z_to_bv 64 (D + i)) = Some (Z_to_bv 8 c8)).
  { intros i Hi. subst M'. rewrite <- (u64_of_Z D HD64) at 2. apply APSX.wbytes_fill_at; [rewrite (u64_of_Z D HD64); clear - A2 XD Hdhi'; lia | exact Hi]. }
  split.
  - split.
    + cbn [after_call s_regs s_next].
      apply (APSX.regs_after_call E (s_regs ss) R regs' nx (Some (reg ss 10)) HR Fsr0 Hkept).
      split; [exact Fdst|]. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha0. rewrite (APSX.w_split_lit_denot E (reg ss 10) db dk Hsd). reflexivity.
    + cbn [after_call s_know]. rewrite MEM.
      eapply APS.know_ok_agree'; [exact Hag | exact Hkv |].
      constructor.
      * destruct (Z.eqb c8 0) eqn:Hz; cbn [kentry_ok]; unfold flat, elenZ; cbn [a_base a_off edenot]; rewrite (u64_of_Z n) by lia;
          change (estart E (SA db dk)) with D.
        -- apply Z.eqb_eq in Hz. split; [clear - HD64 Dhi Hc; lia|]. intros i Hi. rewrite (FILLED i Hi), Hz. reflexivity.
        -- split; [clear - HD64 Dhi Hc; lia|]. intros i Hi. exact (FILLED i Hi).
      * eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wbytes_grows].
        intros x Hx. rewrite Hlen in Hx. subst M'. apply wbytes_out; rewrite ?repeat_length, ?Z2Nat.id, ?u64_of_Z by lia; clear - Hx Hc HD64 Dhi; lia.
  - cbn [after_call s_pc]. rewrite MEM. rewrite Hpc. exact Hms.
Qed.


Fixpoint wslots (m : word -> option byte) (a : Z) (vs : list word) : word -> option byte :=
  match vs with [] => m | v :: r => wslots (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (a + 8) r end.

Lemma wden_wslots_went : forall E M db dk vs acc,
  wden E M (wslots_went db dk vs acc) = wslots (wden E M acc) (estart E (SA db dk)) (map (edenot E) vs).
Proof.
  intros E M db dk vs. revert dk. induction vs as [|v r IH]; intros dk acc; cbn [wslots_went wslots map]; [reflexivity|].
  rewrite IH. cbn [wden]. rewrite APSX.adenot_SA.
  replace (estart E (SA db (dk + 8))) with (estart E (SA db dk) + 8)%Z by (unfold estart; cbn [a_base a_off]; lia).
  reflexivity.
Qed.

Lemma wslots_out : forall vs m a (x : word),
  0 <= a -> a + 8 * Z.of_nat (length vs) <= 2 ^ 64 ->
  (bv_unsigned x < a \/ a + 8 * Z.of_nat (length vs) <= bv_unsigned x) -> wslots m a vs x = m x.
Proof.
  induction vs as [|v r IH]; intros m a x Ha Hnw Hx; cbn [wslots length] in *; [reflexivity|].
  rewrite IH by lia. apply wbytes_out; rewrite length_N_to_le_bytes, (u64_of_Z a) by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Lemma wslots_grows : forall vs m a, mem_grows m (wslots m a vs).
Proof.
  induction vs as [|v r IH]; intros m a; cbn [wslots]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [apply wbytes_grows | apply IH].
Qed.

Lemma wslots_slot : forall vs m a i,
  0 <= a -> a + 8 * Z.of_nat (length vs) <= 2 ^ 64 -> (i < length vs)%nat ->
  rdn segs (wslots m a vs) (Z_to_bv 64 (a + 8 * Z.of_nat i)) 8%nat = Some (word_to_le_bytes 8 (nth i vs (Z_to_bv 64 0))).
Proof.
  induction vs as [|v r IH]; intros m a i Ha Hnw Hi; cbn [wslots length nth] in *; [lia|].
  destruct i as [|i].
  - rewrite Z.mul_0_r, Z.add_0_r.
    rewrite <- (rdn_wbytes_hit8 segs m (Z_to_bv 64 a) v) by (rewrite u64_of_Z by lia; lia).
    apply rdn_ext; [rewrite u64_of_Z by lia; cbn; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia.
    apply wslots_out; cbn in Hx; lia.
  - replace (a + 8 * Z.of_nat (S i))%Z with ((a + 8) + 8 * Z.of_nat i)%Z by lia. apply IH; lia.
Qed.


Lemma ridx_bv5 : forall r : bv 5, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intros r. unfold ridx. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range _ r); lia). apply Z_to_bv_bv_unsigned.
Qed.
Lemma ridx_of_nat : forall i, (i < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat i)) = i.
Proof.
  intros i Hi. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma itab_fact : forall p i, itab_lookup IT p = Some i ->
  exists w, fetch_word segs (Z_to_bv 64 p) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z).
Proof.
  intros p i Hl. pose proof (IT_ok _ _ Hl) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word segs (Z_to_bv 64 p)) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz. injection Hen as ->.
  exists w. split; [reflexivity|]. split; [exact Hec | exact Hd].
Qed.

(* [comment removed for export] *)
Lemma fsd_run : forall (fx : FPState) n p ss tl E R (m : word -> option byte) (D : Z),
  fsd_targets p n ss = Some tl ->
  regs_ok E (s_regs ss) R ->
  (forall j bk, nth_error tl j = Some bk -> estart E (SA (fst bk) (snd bk)) = D + 8 * Z.of_nat j) ->
  0 <= D -> D + 8 * Z.of_nat n < 2 ^ 64 ->
  store_ok segs m (Z_to_bv 64 D) (Z.to_nat (8 * Z.of_nat n)) = true ->
  exists vals, length vals = n /\
    msteps segs (@mkst fx R (Z_to_bv 64 p) m (seg_rom segs))
                (@mkst fx R (Z_to_bv 64 (p + 4 * Z.of_nat n)) (wslots m D vals) (seg_rom segs)).
Proof.
  intros fx n. induction n as [|n IH]; intros p ss tl E R m D Htl HR Hest HD0 HDn Hst.
  - exists []. split; [reflexivity|]. cbn [wslots]. rewrite Z.mul_0_r, Z.add_0_r. apply mst_refl.
  - cbn [fsd_targets] in Htl.
    destruct (itab_lookup IT p) as [i|] eqn:Hl; [|discriminate].
    destruct i; try discriminate. destruct fmt; try discriminate.
    destruct (fsd_targets (p + 4) n ss) as [r|] eqn:Hr; [|discriminate]. injection Htl as <-.
    destruct (itab_fact p _ Hl) as (w & Hf & Hec & Hd).
    pose proof (Hest 0%nat _ eq_refl) as E0. cbn [fst snd] in E0. rewrite Z.mul_0_r, Z.add_0_r in E0.
    set (v := reg_get (@fp_regs fx) rs2).
    assert (Ha : v_addi (getr R rs1) (bv_signed imm) = Z_to_bv 64 D).
    { rewrite (HR rs1). rewrite <- E0.
      destruct (split_lit (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm)))) as [b0 k0] eqn:Hsp.
      cbn [fst snd]. unfold estart. cbn [a_base a_off].
      pose proof (APSX.w_split_lit_denot E _ b0 k0 Hsp) as X. rewrite <- X. rewrite mkAlu_denot. cbn [edenot].
      rewrite alu_add. unfold v_addi, v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
      rewrite Zplus_mod_idemp_r. reflexivity. }
    assert (Hst8 : store_ok segs m (Z_to_bv 64 D) 8%nat = true).
    { eapply (store_ok_sub segs m (Z_to_bv 64 D) (Z_to_bv 64 D) (Z.to_nat (8 * Z.of_nat (S n))) 8%nat); try exact Hst;
        rewrite ?u64_of_Z, ?Z2Nat.id by lia; lia. }
    pose proof (fp_step_fsd fx segs R (Z_to_bv 64 p) m (seg_rom segs) w rs1 rs2 imm (Z_to_bv 64 D) Hf Hec Hd Ha Hst8) as STEP.
    destruct (IH (p + 4) ss r E R (wbytes m (Z_to_bv 64 D) (word_to_le_bytes 8 v)) (D + 8) Hr HR) as (vals & Hlen & Hms).
    + intros j bk Hj. replace (D + 8 + 8 * Z.of_nat j)%Z with (D + 8 * Z.of_nat (S j))%Z by lia. apply Hest. cbn. exact Hj.
    + lia. + lia.
    + eapply store_ok_mono; [apply wbytes_grows|].
      eapply (store_ok_sub segs m (Z_to_bv 64 D) (Z_to_bv 64 (D + 8)) (Z.to_nat (8 * Z.of_nat (S n))) (Z.to_nat (8 * Z.of_nat n))); try exact Hst;
        rewrite ?u64_of_Z, ?Z2Nat.id by lia; lia.
    + exists (v :: vals). split; [cbn; lia|].
      eapply mst_step; [reflexivity | exact STEP |].
      replace (v_addi (Z_to_bv 64 p) 4) with (Z_to_bv 64 (p + 4)).
      2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
          change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
      replace (p + 4 * Z.of_nat (S n))%Z with (p + 4 + 4 * Z.of_nat n)%Z by lia.
      cbn [wslots]. exact Hms.
Qed.

Lemma consecutive_nth : forall l b k j bk, consecutive b k l = true -> nth_error l j = Some bk ->
  fst bk = b /\ snd bk = (k + 8 * Z.of_nat j)%Z.
Proof.
  induction l as [|[b' k'] r IH]; intros b k j bk H Hj; [destruct j; discriminate|].
  cbn [consecutive] in H. apply andb_true_iff in H as [H Hr]. apply andb_true_iff in H as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. subst b' k'.
  destruct j as [|j]; cbn [nth_error] in Hj.
  - injection Hj as <-. cbn [fst snd]. split; [reflexivity | lia].
  - destruct (IH b (k + 8)%Z j bk Hr Hj) as [A B]. split; [exact A | lia].
Qed.

Lemma fsd_targets_length : forall p n ss tl, fsd_targets p n ss = Some tl -> length tl = n.
Proof.
  intros p n. revert p. induction n as [|n IH]; intros p ss tl H; cbn [fsd_targets] in H.
  - injection H as <-. reflexivity.
  - destruct (itab_lookup IT p) as [i|]; [|discriminate]. destruct i; try discriminate. destruct fmt; try discriminate.
    destruct (fsd_targets (p + 4) n ss) as [r|] eqn:Hr; [|discriminate]. injection H as <-. cbn. f_equal. eapply IH. exact Hr.
Qed.

Lemma step_fsdseq_sound : forall (fx : FPState) n ss w ss' w' E R M,
  closed ss w = true -> step_fsdseq n ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx n ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  cbv beta zeta delta [step_fsdseq] in H.
  destruct (fsd_targets (s_pc ss) n ss) as [[|[db dk] rest]|] eqn:Htl; try discriminate.
  destruct (xhi (facts_of (s_know ss)) (mkAlu ALU_ADD db (ELit dk))) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hkv; [|discriminate] end.
  apply some_pair_inj in H as [<- <-].
  apply andb_true_iff in Hc as [Hc Fdb]. apply andb_true_iff in Hc as [Hc Hwr]. apply andb_true_iff in Hc as [Hc Hfd]. apply andb_true_iff in Hc as [Hcons Hdhi'].
  apply Z.ltb_lt in Hdhi'. unfold two64 in Hdhi'. apply andb_true_iff in Hkv as [Hkv Hkvh].
  set (k := s_know ss) in *. set (fk := facts_of k) in *. set (m := wden E M w) in *. set (nx := s_next ss) in *.
  set (len := (8 * Z.of_nat n)%Z) in *.
  pose proof (fsd_targets_length _ _ _ _ Htl) as Hn. cbn [length] in Hn.
  assert (Hnpos : (1 <= n)%nat) by lia.
  pose proof (facts_of_ok segs E m k HK) as HKf. fold fk in HKf.
  assert (Hlen64 : 0 < len < 2 ^ 64).
  { subst len. split; [lia|]. (* [comment removed for export] *)
    pose proof (xhi_sound segs E m fk _ dhi HKf Hdhi) as X. pose proof (u64_range (edenot E (mkAlu ALU_ADD db (ELit dk)))). lia. }
  assert (Hlen : elenZ E (ELit len) = len) by (unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  destruct (APSX.w_flat_x_sound segs E m fk db dk (ELit len) HKf Hfd) as (Dlo & Dhi & _).
  destruct (APSX.kwritable_x_sound segs E m fk k db dk (ELit len) HKf HK Hwr) as (Wst & _ & _).
  change (bv_unsigned (edenot E (ELit len))) with (elenZ E (ELit len)) in Dhi. rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *.
  pose proof (xhi_sound segs E m fk _ dhi HKf Hdhi) as XD.
  rewrite mkAlu_denot in XD. cbn [edenot] in XD. rewrite alu_add in XD. unfold v_add in XD.
  assert (HD64 : 0 <= D < 2 ^ 64) by (clear - Dlo Dhi Hlen64; lia).
  assert (XD' : D <= dhi).
  { unfold D, estart in *. cbn [a_base a_off] in *.
    replace (Z_to_bv 64 (bv_unsigned (edenot E db) + bv_unsigned (Z_to_bv 64 dk)))
      with (Z_to_bv 64 (bv_unsigned (edenot E db) + dk)) in XD.
    2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity. }
    rewrite u64_of_Z in XD by exact HD64. exact XD. }
  (* [comment removed for export] *)
  assert (EST : forall j bk, nth_error ((db, dk) :: rest) j = Some bk -> estart E (SA (fst bk) (snd bk)) = D + 8 * Z.of_nat j).
  { intros [|j] bk Hj.
    - cbn in Hj. injection Hj as <-. cbn [fst snd]. lia.
    - cbn [nth_error] in Hj. destruct (consecutive_nth _ _ _ _ _ Hcons Hj) as [A B].
      destruct bk as [b' k']. cbn [fst snd] in *. subst b' k'. unfold D, estart. cbn [a_base a_off]. lia. }
  destruct (fsd_run fx n (s_pc ss) ss _ E R m D Htl HR EST ltac:(lia) ltac:(clear - XD' Hdhi' HD64; lia)
              ltac:(apply Wst; subst len; rewrite Z2Nat.id by lia; lia)) as (vals & Hvl & Hms).
  (* [comment removed for export] *)
  set (E' := APS.ext_list E nx vals).
  pose proof (APS.ext_list_agree E nx vals) as Hag. fold E' in Hag.
  exists fx, E', R. split; [exact Hag|]. split; [cbn [s_next]; lia|].
  assert (Hw : wden E' M w = m) by (symmetry; eapply wden_agree; [exact Hag | exact Fw]).
  assert (ED : estart E' (SA db dk) = D).
  { unfold estart. cbn [a_base a_off]. rewrite <- (edenot_agree_AP nx E E' db Hag Fdb). reflexivity. }
  assert (VALS : map (edenot E') (map (fun j => EVar (nx + j)%nat) (seq 0 n)) = vals).
  { rewrite map_map. rewrite <- (map_id vals). rewrite <- Hvl.
    transitivity (map (fun j => nth j vals (Z_to_bv 64 0)) (seq 0 (length vals))).
    - apply map_ext_in. intros j Hj. apply in_seq in Hj. cbn [edenot]. unfold E'. apply APS.ext_list_at. lia.
    - rewrite map_id. clear. induction vals as [|v r IH]; [reflexivity|].
      cbn [length]. rewrite <- cons_seq. cbn [map nth]. f_equal.
      rewrite <- seq_shift, map_map. cbn [nth]. exact IH. }
  assert (MEM : wden E' M (wslots_went db dk (map (fun j => EVar (nx + j)%nat) (seq 0 n)) w) = wslots m D vals).
  { rewrite wden_wslots_went, Hw, ED, VALS. reflexivity. }
  split.
  - split.
    + cbn [s_regs]. eapply APS.regs_ok_agree'; [exact Hag | exact Fsr0 | exact HR].
    + cbn [s_know]. rewrite MEM. apply Forall_app. split.
      * assert (SL : forall vs dk0 i0, (i0 + length vs = n)%nat -> estart E' (SA db dk0) = D + 8 * Z.of_nat i0 ->
                     (forall j, (j < length vs)%nat -> edenot E' (nth j vs (ELit 0)) = nth (i0 + j) vals (Z_to_bv 64 0)) ->
                     know_ok segs E' (wslots m D vals) (kslots db dk0 vs)).
        { induction vs as [|v r IH]; intros dk0 i0 Hl He Hv; cbn [kslots]; [constructor|].
          cbn [length] in Hl. constructor.
          - cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite He; clear - HD64 Hl XD' Hdhi'; lia|].
            rewrite APSX.adenot_SA, He. pose proof (Hv 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. rewrite H0, Nat.add_0_r.
            apply wslots_slot; [lia | rewrite Hvl; clear - HD64 XD' Hdhi'; lia | rewrite Hvl; lia].
          - apply (IH (dk0 + 8) (S i0)); [lia | unfold estart in *; cbn [a_base a_off] in *; lia |].
            intros j Hj. replace (S i0 + j)%nat with (i0 + S j)%nat by lia. apply (Hv (S j)). cbn [length]. lia. }
        apply (SL _ dk 0%nat).
        -- rewrite length_map, length_seq. reflexivity.
        -- rewrite ED. lia.
        -- intros j Hj. cbn [Nat.add]. rewrite <- VALS.
           change (Z_to_bv 64 0) with (edenot E' (ELit 0)). rewrite map_nth. reflexivity.
      * eapply APS.know_ok_agree'; [exact Hag | exact Hkvh |].
        eapply APSX.w_know_ok_havoc; [apply kimg_precut_ok; exact HK | | apply wslots_grows].
        intros x Hx. rewrite Hlen in Hx. apply wslots_out; rewrite ?Hvl; clear - Hx HD64 XD' Hdhi'; subst len; lia.
  - cbn [s_pc]. rewrite MEM. exact Hms.
Qed.

(* [comment removed for export] *)
Lemma fld_run : forall n (fx : FPState) p ss E R (m : word -> option byte) allkn,
  fld_sources_ok p n ss = true ->
  regs_ok E (s_regs ss) R -> know_ok segs E m allkn -> allkn = s_know ss ->
  exists fx' : FPState,
    msteps segs (@mkst fx R (Z_to_bv 64 p) m (seg_rom segs))
                (@mkst fx' R (Z_to_bv 64 (p + 4 * Z.of_nat n)) m (seg_rom segs)).
Proof.
  induction n as [|n IH]; intros fx p ss E R m allkn H HR HK Hak.
  - exists fx. rewrite Z.mul_0_r, Z.add_0_r. apply mst_refl.
  - cbn [fld_sources_ok] in H.
    destruct (itab_lookup IT p) as [i|] eqn:Hl; [|discriminate].
    destruct i; try discriminate. destruct fmt; try discriminate.
    apply andb_true_iff in H as [Hrd Hrest].
    destruct (itab_fact p _ Hl) as (w & Hf & Hec & Hd).
    subst allkn.
    destruct (kn_readable_sound segs E m (facts_of (s_know ss)) m (s_know ss) _ _ 8 (facts_of_ok segs E m _ HK) HK
                ltac:(lia) ltac:(lia) Hrd) as (Hfl & bs & Hbs & Hlbs).
    assert (Ha : v_addi (getr R rs1) (bv_signed imm) = adenot E (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm))).
    { rewrite (HR rs1). rewrite to_saddr_denot. reflexivity. }
    pose proof (fp_step_fld fx segs R (Z_to_bv 64 p) m (seg_rom segs) w rd rs1 imm _ bs Hf Hec Hd Ha Hbs) as STEP.
    destruct (IH (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                 (p + 4) ss E R m (s_know ss) Hrest HR HK eq_refl) as (fx' & Hms).
    exists fx'. eapply mst_step; [reflexivity | exact STEP |].
    replace (v_addi (Z_to_bv 64 p) 4) with (Z_to_bv 64 (p + 4)).
    2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
        change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
    replace (p + 4 * Z.of_nat (S n))%Z with (p + 4 + 4 * Z.of_nat n)%Z by lia. exact Hms.
Qed.

Lemma step_fldseq_sound : forall (fx : FPState) n ss w ss' w' E R M,
  closed ss w = true -> step_fldseq n ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx n ss w ss' w' E R M Hcl H [HR HK]. unfold step_fldseq in H.
  destruct (fld_sources_ok (s_pc ss) n ss) eqn:Hs; [|discriminate]. apply some_pair_inj in H as [<- <-].
  destruct (fld_run n fx (s_pc ss) ss E R (wden E M w) (s_know ss) Hs HR HK eq_refl) as (fx' & Hms).
  exists fx', E, R. split; [apply APS.env_agree_refl|]. split; [cbn [s_next]; lia|].
  split; [split; [exact HR | exact HK]|]. cbn [s_pc]. exact Hms.
Qed.

(* [comment removed for export] *)
Definition strlen_step_stmt : Prop := forall (fx : FPState) kz ss w ss' w' E R M,
  closed ss w = true -> step_strlen kz ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).

(* [comment removed for export] *)
Lemma efold_denot : forall E x k e, edenot E (efold x k e) = edenot (APS.upd E x (Z_to_bv 64 k)) e.
Proof.
  intros E x k e. induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n];
    cbn [efold edenot]; try reflexivity.
  - unfold APS.upd. cbn [ev]. destruct (Nat.eqb n x); reflexivity.
  - rewrite mkAlu_denot, IHa, IHb. reflexivity.
  - rewrite mkAluw_denot, IHa, IHb. reflexivity.
  - rewrite mkMd_denot, IHa, IHb. reflexivity.
  - rewrite mkMdw_denot, IHa, IHb. reflexivity.
  - destruct (Nat.leb n 8) eqn:Hn.
    + apply Nat.leb_le in Hn. rewrite mkExt_denot by exact Hn. rewrite IHa. reflexivity.
    + cbn [edenot]. rewrite IHa. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evars_mono : forall e acc l, evars e acc = Some l -> exists l0, acc = Some l0 /\ incl l0 l.
Proof.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; intros acc l H;
    destruct acc as [l0|]; cbn [evars] in H; try discriminate;
    try (destruct (IHb _ _ H) as (l1 & H1 & S1); destruct (IHa _ _ H1) as (l2 & H2 & S2); injection H2 as <-;
         exists l0; split; [reflexivity | eapply incl_tran; [exact S2 | exact S1]]).
  - injection H as <-. exists l0. split; [reflexivity | apply incl_refl].
  - injection H as <-. exists l0. split; [reflexivity|]. intros m Hm. destruct (existsb (Nat.eqb n) l0); [exact Hm | right; exact Hm].
  - exact (IHa _ _ H).
Qed.

Lemma evars_agree : forall e acc l E E',
  evars e acc = Some l -> (forall n, In n l -> ev E n = ev E' n) -> eb E = eb E' -> edenot E e = edenot E' e.
Proof.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx kk i n]; intros acc l E E' H Hv Hb;
    destruct acc as [l0|]; cbn [evars edenot] in *; try discriminate; try reflexivity;
    try (destruct (evars_mono b _ _ H) as (l1 & H1 & S1);
         rewrite (IHa _ _ E E' H1), (IHb _ _ E E' H); [reflexivity | exact Hv | exact Hb | intros m Hm; apply Hv; apply S1; exact Hm | exact Hb]).
  - injection H as <-. apply Hv. destruct (existsb (Nat.eqb n) l0) eqn:Hx.
    + apply existsb_exists in Hx as (m & Hm & He). apply Nat.eqb_eq in He. subst m. exact Hm.
    + left. reflexivity.
  - first [rewrite (IHa _ _ E E' H Hv Hb); reflexivity | rewrite Hb; reflexivity].
Qed.

Lemma zseq_In : forall lo n v, lo <= v < lo + Z.of_nat n -> In v (zseq lo n).
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo v Hv; [lia|]. cbn [zseq].
  destruct (Z.eq_dec v lo) as [->|Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

Lemma eval_range_sound : forall E M k e c,
  know_ok segs E M k -> eval_range k e = Some c -> edenot E e = Z_to_bv 64 c.
Proof.
  intros E M k e c HK H. unfold eval_range in H.
  destruct (evars e (Some [])) as [[|x [|]]|] eqn:Hev; try discriminate.
  destruct (erange k (EVar x)) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct (Z.leb lo hi && Z.leb (hi - lo) EVMAX)%bool eqn:Hb; [|discriminate].
  apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  destruct (efold x lo e) as [c0| | | | | | |] eqn:Hf; try discriminate.
  match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hall; [|discriminate] end.
  injection H as <-.
  pose proof (erange_sound segs E M k (EVar x) lo hi HK Her) as Hx. cbn [edenot] in Hx.
  set (v := bv_unsigned (ev E x)) in *.
  assert (Hin : In v (zseq lo (Z.to_nat (hi - lo + 1)))).
  { apply zseq_In. rewrite Z2Nat.id by lia. clear - Hx Hb1. lia. }
  rewrite forallb_forall in Hall. specialize (Hall v Hin).
  apply expr_eqb_eq in Hall.
  transitivity (edenot (APS.upd E x (Z_to_bv 64 v)) e).
  - eapply evars_agree; [exact Hev | | reflexivity]. intros n Hn. destruct Hn as [<-|[]].
    unfold APS.upd. cbn [ev]. rewrite Nat.eqb_refl. subst v. symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite <- efold_denot, Hall. reflexivity.
Qed.

Lemma step_evalreg_sound : forall (fx : FPState) r ss w ss' w' E R M,
  closed ss w = true -> step_evalreg r ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx r ss w ss' w' E R M Hcl H [HR HK]. unfold step_evalreg in H.
  destruct (Nat.ltb 0 r && Nat.ltb r 32)%bool eqn:Hr; [|discriminate].
  apply andb_true_iff in Hr as [Hr0 Hr32]. apply Nat.ltb_lt in Hr0. apply Nat.ltb_lt in Hr32.
  destruct (eval_range (s_know ss) (reg ss r)) as [c|] eqn:Hev; [|discriminate]. injection H as <- <-.
  exists fx, E, R. split; [apply APS.env_agree_refl|]. split; [cbn [s_next]; lia|]. split.
  - split; [|cbn [s_know]; exact HK]. cbn [s_regs].
    pose proof (eval_range_sound E _ (s_know ss) (reg ss r) c HK Hev) as Hc.
    intros r'. unfold sr_get. destruct (bv_eqb r' 0) eqn:Hr'0.
    + specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR. exact HR.
    + rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') r) eqn:Hi.
      * apply Nat.eqb_eq in Hi. specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR.
        rewrite HR. unfold reg in Hc. rewrite <- Hi in Hc. rewrite Hc. reflexivity.
      * specialize (HR r'). unfold sr_get in HR. rewrite Hr'0 in HR. exact HR.
  - cbn [s_pc]. apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma join_regs_sound : forall ra rb i nx rj nx' E (G : nat -> word) (side : bool),
  join_regs i ra rb nx = (rj, nx') -> length rb = length ra ->
  (forall j, (j < length ra)%nat -> G (i + j)%nat = edenot E (nth j (if side then ra else rb) (ELit 0))) ->
  (forall j, (j < length ra)%nat -> APC.expr_vars_lt nx (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt nx (nth j rb (ELit 0)) = true) ->
  exists E', env_agree nx E E' /\ (nx <= nx')%nat /\ length rj = length ra
    /\ (forall j, (j < length ra)%nat -> G (i + j)%nat = edenot E' (nth j rj (ELit 0))).
Proof.
  induction ra as [|a ra IH]; intros rb i nx rj nx' E G side H Hlen HG Hv.
  - cbn [join_regs] in H. injection H as <- <-. exists E. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [reflexivity|].
    intros j Hj. cbn in Hj. lia.
  - destruct rb as [|b rb]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen. cbn [join_regs] in H.
    assert (HG' : forall j, (j < length ra)%nat -> G (S i + j)%nat = edenot E (nth j (if side then ra else rb) (ELit 0))).
    { intros j Hj. replace (S i + j)%nat with (i + S j)%nat by lia. rewrite (HG (S j)) by (cbn; lia). destruct side; reflexivity. }
    assert (Hv' : forall j, (j < length ra)%nat -> APC.expr_vars_lt nx (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt nx (nth j rb (ELit 0)) = true).
    { intros j Hj. exact (Hv (S j) ltac:(cbn; lia)). }
    destruct (Hv 0%nat ltac:(cbn; lia)) as [Hva Hvb]. cbn [nth] in Hva, Hvb.
    pose proof (HG 0%nat ltac:(cbn; lia)) as HG0. rewrite Nat.add_0_r in HG0. cbn [nth] in HG0.
    destruct (expr_eqb a b) eqn:Hab.
    + destruct (join_regs (S i) ra rb nx) as [r n] eqn:Hr. injection H as <- <-.
      destruct (IH rb (S i) nx r n E G side Hr Hlen HG' Hv') as (E' & Hag & Hle & Hlr & HR).
      exists E'. split; [exact Hag|]. split; [exact Hle|]. split; [cbn; lia|].
      intros [|j] Hj; cbn [nth].
      * rewrite Nat.add_0_r. rewrite HG0. apply expr_eqb_eq in Hab. subst b.
        destruct side; (eapply edenot_agree_AP; [exact Hag | first [exact Hva | exact Hvb]]).
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply HR. cbn in Hj. lia.
    + destruct (join_regs (S i) ra rb (S nx)) as [r n] eqn:Hr. injection H as <- <-.
      set (E1 := APS.upd E nx (G i)).
      assert (Hag1 : env_agree nx E E1).
      { split; [|reflexivity]. intros m Hm. unfold E1, APS.upd. cbn [ev]. destruct (Nat.eqb m nx) eqn:He; [apply Nat.eqb_eq in He; lia | reflexivity]. }
      assert (HG1 : forall j, (j < length ra)%nat -> G (S i + j)%nat = edenot E1 (nth j (if side then ra else rb) (ELit 0))).
      { intros j Hj. rewrite (HG' j Hj). destruct (Hv' j Hj) as [X Y].
        destruct side; (eapply edenot_agree_AP; [exact Hag1 | first [exact X | exact Y]]). }
      assert (Hv1 : forall j, (j < length ra)%nat -> APC.expr_vars_lt (S nx) (nth j ra (ELit 0)) = true /\ APC.expr_vars_lt (S nx) (nth j rb (ELit 0)) = true).
      { intros j Hj. destruct (Hv' j Hj) as [X Y]. split; (eapply APS.expr_vars_lt_mono; [eassumption | lia]). }
      destruct (IH rb (S i) (S nx) r n E1 G side Hr Hlen HG1 Hv1) as (E' & Hag & Hle & Hlr & HR).
      exists E'. split.
      { eapply APS.env_agree_trans; [exact Hag1 | eapply APS.env_agree_le; [exact Hag | lia]]. }
      split; [lia|]. split; [cbn; lia|].
      intros [|j] Hj; cbn [nth].
      * rewrite Nat.add_0_r. cbn [edenot]. destruct Hag as [Hagv _]. rewrite <- (Hagv nx) by lia. unfold E1, APS.upd. cbn [ev]. rewrite Nat.eqb_refl. reflexivity.
      * replace (i + S j)%nat with (S i + j)%nat by lia. apply HR. cbn in Hj. lia.
Qed.

Lemma arm_ok_parts : forall joinpc nx sa, arm_ok joinpc nx sa = true ->
  s_pc sa = joinpc /\ s_log sa = [] /\ s_next sa = nx /\ APC.sr_vars_lt nx (s_regs sa) = true /\ length (s_regs sa) = 32%nat
  /\ nth 0 (s_regs sa) (ELit 0) = ELit 0.
Proof.
  intros joinpc nx sa H. unfold arm_ok in H.
  apply andb_true_iff in H as [H Hr0]. apply andb_true_iff in H as [H Hlen]. apply andb_true_iff in H as [H Hvars].
  apply andb_true_iff in H as [H Hnx]. apply andb_true_iff in H as [Hpc Hlog].
  apply Z.eqb_eq in Hpc. apply Nat.eqb_eq in Hnx. apply Nat.eqb_eq in Hlen.
  destruct (s_log sa); [|discriminate].
  split; [exact Hpc|]. split; [reflexivity|]. split; [exact Hnx|]. split; [exact Hvars|]. split; [exact Hlen|].
  destruct (s_regs sa) as [|[z| | | | | | |] t]; try discriminate. destruct z; try discriminate. reflexivity.
Qed.

Lemma step_diamond_sound : forall (fx : FPState) jp ss w ss' w' E R M,
  closed ss w = true -> step_diamond jp ss w = Some (ss', w') -> INV E ss w R M ->
  STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx jp ss w ss' w' E R M Hcl H [HR HK].
  pose proof Hcl as Hcl0. unfold closed in Hcl0.
  apply andb_true_iff in Hcl0 as [Hcl0 _]. apply andb_true_iff in Hcl0 as [Hcl0 Fw0]. apply andb_true_iff in Hcl0 as [Fsr0 Fkn0].
  destruct (closed_parts ss w Hcl) as (Fsr & Fkn & Fw & Flog).
  unfold step_diamond in H.
  destruct (APC.branch_probe IT (acs_of ss)) as [e|] eqn:Hbp; [|discriminate].
  destruct (erange (s_know ss) e) as [[lo hi]|] eqn:Her; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hok; [|discriminate] end.
  apply andb_true_iff in Hok as [Hok Hokb]. apply andb_true_iff in Hok as [Hve Hoka].
  set (sa := sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] (KRange e lo 0 :: s_know ss) (s_next ss))) in *.
  set (sb := sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] (KRange e 1 hi :: s_know ss) (s_next ss))) in *.
  destruct (join_regs 0 (s_regs sa) (s_regs sb) (s_next ss)) as [rj nx'] eqn:Hjoin. injection H as <- <-.
  destruct (arm_ok_parts _ _ _ Hoka) as (PCa & LOGa & NXa & Va & La & Z0a).
  destruct (arm_ok_parts _ _ _ Hokb) as (PCb & LOGb & NXb & Vb & Lb & Z0b).
  set (m := wden E M w) in *.
  pose proof (erange_sound segs E m (s_know ss) e lo hi HK Her) as Hrange.
  (* [comment removed for export] *)
  assert (ARM : exists (side : bool) (sx : sym_state), (sx = (if side then sa else sb))
            /\ know_ok segs E m ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss)).
  { destruct (Z_le_gt_dec (bv_unsigned (edenot E e)) 0) as [Hle|Hgt].
    - exists true, sa. split; [reflexivity|]. constructor; [cbn [kentry_ok]; lia | exact HK].
    - exists false, sb. split; [reflexivity|]. constructor; [cbn [kentry_ok]; lia | exact HK]. }
  destruct ARM as (side & sx & Hsx & HKx).
  assert (Fknx : AxSymRun3.kn_vars_lt (s_next ss) ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss) = true).
  { destruct side; cbn [AxSymRun3.kn_vars_lt AxSymRun3.kentry_vars_lt]; rewrite Hve, Fkn; reflexivity. }
  pose proof (@runTX_sound fx segs IT 0%nat BFUEL [jp] (s_pc ss) (s_regs ss) _ (s_next ss) E m (seg_rom segs) R IT_ok HR HKx Fsr Fknx) as X.
  cbn zeta in X.
  replace (sym_execTX segs IT 0%nat BFUEL true [jp] (SS (s_pc ss) (s_regs ss) [] ((if side then KRange e lo 0 else KRange e 1 hi) :: s_know ss) (s_next ss)))
    with sx in X by (subst sx; destruct side; reflexivity).
  destruct X as (E1 & R1 & Hag1 & Hle1 & HR1 & Hlf1 & HK1 & Hms1 & _).
  assert (PCx : s_pc sx = jp) by (subst sx; destruct side; assumption).
  assert (LOGx : s_log sx = []) by (subst sx; destruct side; assumption).
  assert (NXx : s_next sx = s_next ss) by (subst sx; destruct side; assumption).
  rewrite LOGx in Hms1. cbn [mem_denot] in Hms1. rewrite PCx in Hms1.
  (* [comment removed for export] *)
  set (G := fun n : nat => getr R1 (Z_to_bv 5 (Z.of_nat n))).
  assert (HG : forall j, (j < length (s_regs sa))%nat -> G (0 + j)%nat = edenot E1 (nth j (if side then s_regs sa else s_regs sb) (ELit 0))).
  { intros j Hj. unfold G. cbn [Nat.add]. rewrite (HR1 (Z_to_bv 5 (Z.of_nat j))). unfold sr_get.
    rewrite La in Hj.
    destruct (Nat.eq_dec j 0) as [->|Hj0].
    - replace (bv_eqb (Z_to_bv 5 (Z.of_nat 0)) 0) with true by reflexivity. cbn [edenot].
      replace (nth 0 (if side then s_regs sa else s_regs sb) (ELit 0)) with (ELit 0) by (destruct side; symmetry; assumption). reflexivity.
    - replace (bv_eqb (Z_to_bv 5 (Z.of_nat j)) 0) with false.
      2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
          rewrite Z.mod_small by lia. change (bv_unsigned (0%bv : bv 5)) with 0%Z. lia. }
      rewrite ridx_of_nat by lia. subst sx. destruct side; reflexivity. }
  assert (Hv : forall j, (j < length (s_regs sa))%nat -> APC.expr_vars_lt (s_next ss) (nth j (s_regs sa) (ELit 0)) = true
                                                  /\ APC.expr_vars_lt (s_next ss) (nth j (s_regs sb) (ELit 0)) = true).
  { intros j Hj. rewrite La in Hj. split; (apply nth_sr_vars_lt; [assumption | lia]). }
  assert (Hlen : length (s_regs sb) = length (s_regs sa)) by (rewrite La, Lb; reflexivity).
  destruct (join_regs_sound (s_regs sa) (s_regs sb) 0 (s_next ss) rj nx' E1 G side Hjoin Hlen HG Hv) as (E' & Hag' & Hle' & Hlr & HRj).
  exists fx, E', R1.
  split; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag']|]. split; [cbn [s_next]; lia|].
  assert (Hw : wden E' M w = m) by (symmetry; eapply wden_agree; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag'] | exact Fw]).
  split.
  - split; cbn [s_regs s_know].
    + intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
      * unfold bv_eqb in Hr0. apply Z.eqb_eq in Hr0. replace r with (Z_to_bv 5 (Z.of_nat 0)) by (apply bv_eq; rewrite Hr0; reflexivity).
        pose proof (HG 0%nat ltac:(rewrite La; lia)) as X. unfold G in X. cbn [Nat.add] in X. rewrite X.
        replace (nth 0 (if side then s_regs sa else s_regs sb) (ELit 0)) with (ELit 0) by (destruct side; symmetry; assumption). reflexivity.
      * assert (Hr : (ridx r < 32)%nat) by (unfold ridx; pose proof (bv_unsigned_in_range _ r); change (bv_modulus 5) with 32%Z in *; lia).
        pose proof (HRj (ridx r) ltac:(rewrite La; exact Hr)) as X. unfold G in X. cbn [Nat.add] in X. rewrite ridx_bv5 in X. exact (X).
    + rewrite Hw. eapply APS.know_ok_agree'; [eapply APS.env_agree_trans; [exact Hag1 | exact Hag'] | exact Fkn0 | exact HK].
  - cbn [s_pc]. rewrite Hw. exact Hms1.
Qed.

(* [comment removed for export] *)
Definition step_req (st : sstep) : Prop := match st with SStrlen _ => strlen_step_stmt | _ => True end.
Definition no_strlen (steps : list sstep) : bool :=
  forallb (fun st => match st with SStrlen _ => false | _ => true end) steps.
Lemma no_strlen_req : forall steps, no_strlen steps = true -> Forall step_req steps.
Proof.
  intros steps H. unfold no_strlen in H. rewrite forallb_forall in H. apply Forall_forall. intros st Hin.
  specialize (H st Hin). destruct st; cbn; try exact I. discriminate.
Qed.

Lemma seg_step_sound : forall (fx : FPState) st ss w ss' w' E R M,
  step_req st ->
  seg_step st ss w = Some (ss', w') -> INV E ss w R M -> STEP_POST fx ss w ss' w' E R M (seg_rom segs).
Proof.
  intros fx st ss w ss' w' E R M Hreq H HI. unfold seg_step in H.
  destruct (closed ss w) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  destruct st as [stops| | |n|n|kz|p|jp|r].
  - eapply step_block_sound; eassumption.
  - eapply step_copy_sound; eassumption.
  - eapply step_fill_sound; eassumption.
  - eapply step_fsdseq_sound; eassumption.
  - eapply step_fldseq_sound; eassumption.
  - eapply Hreq; eassumption.
  - destruct (Z.eqb (s_pc ss) p); [|discriminate]. injection H as <- <-.
    exists fx, E, R. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [exact HI | apply mst_refl].
  - eapply step_diamond_sound; eassumption.
  - eapply step_evalreg_sound; eassumption.
Qed.

Theorem seg_run_sound : forall (fx : FPState) steps ss w ss' w' E R M,
  Forall step_req steps ->
  seg_run steps ss w = Some (ss', w') -> INV E ss w R M ->
  exists (fx' : FPState) E' R', env_agree (s_next ss) E E' /\ (s_next ss <= s_next ss')%nat /\ INV E' ss' w' R' M
    /\ closed ss' w' = true
    /\ msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) (wden E M w) (seg_rom segs))
                   (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (wden E' M w') (seg_rom segs)).
Proof.
  intros fx steps. revert fx. induction steps as [|st rest IH]; intros fx ss w ss' w' E R M Hreq H HI; cbn [seg_run] in H.
  - destruct (closed ss w) eqn:Hcl; [|discriminate]. injection H as <- <-.
    exists fx, E, R. split; [apply APS.env_agree_refl|]. split; [lia|]. split; [exact HI|]. split; [exact Hcl | apply mst_refl].
  - apply Forall_cons_iff in Hreq as [Hreq1 Hreqr].
    destruct (seg_step st ss w) as [[ss1 w1]|] eqn:Hs; [|discriminate].
    destruct (seg_step_sound fx st ss w ss1 w1 E R M Hreq1 Hs HI) as (fx1 & E1 & R1 & Hag1 & Hle1 & HI1 & Hms1).
    destruct (IH fx1 ss1 w1 ss' w' E1 R1 M Hreqr H HI1) as (fx2 & E2 & R2 & Hag2 & Hle2 & HI2 & Hcl2 & Hms2).
    exists fx2, E2, R2. split; [eapply APS.env_agree_trans; [exact Hag1 | eapply APS.env_agree_le; [exact Hag2 | exact Hle1]]|].
    split; [lia|]. split; [exact HI2|]. split; [exact Hcl2|].
    eapply msteps_trans; [exact Hms1 | exact Hms2].
Qed.

(* [comment removed for export] *)
Corollary seg_run_entry : forall (fx : FPState) steps pc kn nx ss' w' R M,
  Forall step_req steps ->
  seg_run steps (SS pc sr_id [] kn nx) [] = Some (ss', w') ->
  know_ok segs (EnvR R) M kn ->
  exists (fx' : FPState) E' R', env_agree nx (EnvR R) E' /\ regs_ok E' (s_regs ss') R' /\ know_ok segs E' (wden E' M w') (s_know ss')
    /\ closed ss' w' = true
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (s_pc ss')) (wden E' M w') (seg_rom segs)).
Proof.
  intros fx steps pc kn nx ss' w' R M Hreq H HK.
  destruct (seg_run_sound fx steps (SS pc sr_id [] kn nx) [] ss' w' (EnvR R) R M Hreq H) as (fx' & E' & R' & Hag & _ & [HR' HK'] & Hcl & Hms).
  - split; [apply EnvR_regs_ok | cbn [wden]; exact HK].
  - exists fx', E', R'. cbn [s_next s_pc wden] in *. split; [exact Hag|]. split; [exact HR'|]. split; [exact HK'|]. split; [exact Hcl | exact Hms].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition region : Type := (expr * Z * Z)%type.
Definition within1 (b : expr) (k len : Z) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in (expr_eqb b rb && Z.ltb 0 len && Z.leb rlo k && Z.leb (k + len) (rlo + rlen))%bool.
Definition went_within (F : list region) (g : went) : bool :=
  match g with
  | WSt (SA b k) wd _ => existsb (within1 b k (Z.of_nat wd)) F
  | WCopy db dk _ _ n => Z.leb 0 n && existsb (within1 db dk n) F
  | WFill db dk n _ => Z.leb 0 n && existsb (within1 db dk n) F
  end%bool.
Definition regions_flat (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ estart E (SA rb rlo) + rlen <= 2 ^ 64) F.
Definition outside (E : env) (F : list region) (a : word) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            bv_unsigned a < estart E (SA rb rlo) \/ estart E (SA rb rlo) + rlen <= bv_unsigned a) F.

Lemma within1_sound : forall E b k len rb rlo rlen (a : word),
  within1 b k len (rb, rlo, rlen) = true ->
  (bv_unsigned a < estart E (SA rb rlo) \/ estart E (SA rb rlo) + rlen <= bv_unsigned a) ->
  bv_unsigned a < estart E (SA b k) \/ estart E (SA b k) + len <= bv_unsigned a.
Proof.
  intros E b k len rb rlo rlen a H Ha. unfold within1 in H.
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H H1]. apply andb_true_iff in H as [Hb H0].
  apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb.
  unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma wden_frame : forall E M w F (a : word),
  forallb (went_within F) w = true -> regions_flat E F -> outside E F a ->
  wden E M w a = M a.
Proof.
  intros E M w F a Hw HF Ha. induction w as [|g r IH]; [reflexivity|].
  cbn [forallb] in Hw. apply andb_true_iff in Hw as [Hg Hr]. specialize (IH Hr).
  assert (REG : forall b k len, existsb (within1 b k len) F = true -> 0 <= len ->
            0 <= estart E (SA b k) /\ estart E (SA b k) + len <= 2 ^ 64 /\ 0 < len
            /\ (bv_unsigned a < estart E (SA b k) \/ estart E (SA b k) + len <= bv_unsigned a)).
  { intros b k len Hex Hlen. apply existsb_exists in Hex as ([[rb rlo] rlen] & Hin & Hw1).
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hfl. pose proof (proj1 (Forall_forall _ _) Ha _ Hin) as Hout.
    cbn beta iota in Hfl, Hout.
    pose proof (within1_sound E b k len rb rlo rlen a Hw1 Hout) as X.
    unfold within1 in Hw1. apply andb_true_iff in Hw1 as [Hw1 H2]. apply andb_true_iff in Hw1 as [Hw1 H1]. apply andb_true_iff in Hw1 as [Hb H0].
    apply expr_eqb_eq in Hb. apply Z.ltb_lt in H0. apply Z.leb_le in H1. apply Z.leb_le in H2. subst rb.
    unfold estart in *. cbn [a_base a_off] in *. lia. }
  destruct g as [[b k] wd v|db dk sb sk n|db dk n c]; cbn [wden went_within] in *.
  - destruct (REG b k (Z.of_nat wd) Hg ltac:(lia)) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite length_N_to_le_bytes, APSX.adenot_SA, u64_of_Z by lia; lia.
  - apply andb_true_iff in Hg as [Hn Hg]. apply Z.leb_le in Hn.
    destruct (REG db dk n Hg Hn) as (R0 & R1 & RP & R2).
    destruct (rdn segs (wden E M r) (adenot E (SA sb sk)) (Z.to_nat n)) as [bs|] eqn:Hrd; [|exact IH].
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlbs.
    rewrite wbytes_out; [exact IH | |]; rewrite Hlbs, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
  - apply andb_true_iff in Hg as [Hn Hg]. apply Z.leb_le in Hn.
    destruct (REG db dk n Hg Hn) as (R0 & R1 & RP & R2).
    rewrite wbytes_out; [exact IH | |]; rewrite repeat_length, APSX.adenot_SA, Z2Nat.id, u64_of_Z by lia; lia.
Qed.

(* [comment removed for export] *)
Fixpoint kn_word (kn : list kentry) (b : expr) (k : Z) (w : nat) : option expr :=
  match kn with
  | [] => None
  | KWord (SA b' k') w' v :: r => if (expr_eqb b' b && Z.eqb k' k && Nat.eqb w' w)%bool then Some v else kn_word r b k w
  | _ :: r => kn_word r b k w
  end.
Lemma kn_word_sound : forall E M kn b k w v,
  know_ok segs E M kn -> kn_word kn b k w = Some v ->
  rdn segs M (adenot E (SA b k)) w = Some (word_to_le_bytes w (edenot E v)).
Proof.
  intros E M kn b k w v HK H. induction kn as [|K r IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [kn_word] in H.
  destruct K as [[b' k'] w' v'| | | | | | | | |]; try exact (IH Hr H).
  destruct (expr_eqb b' b && Z.eqb k' k && Nat.eqb w' w)%bool eqn:Hc; [|exact (IH Hr H)].
  injection H as <-. apply andb_true_iff in Hc as [Hc Hw]. apply andb_true_iff in Hc as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. apply Nat.eqb_eq in Hw. subst b' k' w'.
  cbn [kentry_ok] in HKK. destruct HKK as (_ & _ & Hrd). exact Hrd.
Qed.

(* [comment removed for export] *)
Record post_spec : Type := PS {
  ps_pc : Z;
  ps_regs : list (nat * expr);                 (* [comment removed for export] *)
  ps_regions : list region;                    (* [comment removed for export] *)
  ps_cells : list kentry                       (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition region_flat_chk (kn : list kentry) (r : region) : bool :=
  let '(rb, rlo, rlen) := r in
  match rb with
  | ELit 0 => (Z.leb 0 rlo && Z.ltb 0 rlen && Z.ltb (rlo + rlen) two64)%bool
  | _ => (Z.ltb 0 rlen && existsb (fun K => match K with
                         | KWr (SA b lo) (ELit len) => (expr_eqb b rb && Z.leb lo rlo && Z.leb (rlo + rlen) (lo + len) && Z.ltb len two64 && Z.leb 0 len)%bool
                         | _ => false end) kn)%bool
  end.
Definition post_ok (ps : post_spec) (ss : sym_state) (w : list went) : bool :=
  (Z.eqb (s_pc ss) (ps_pc ps)
   && forallb (fun ie : nat * expr => expr_eqb (nth (fst ie) (s_regs ss) (ELit 0)) (snd ie)) (ps_regs ps)
   && forallb (went_within (ps_regions ps)) w
   && forallb (region_flat_chk (s_know ss)) (ps_regions ps)
   && forallb (fun K => existsb (APC.kentry_eqb K) (s_know ss)) (ps_cells ps))%bool.

Definition run_post_ok (steps : list sstep) (ss0 : sym_state) (ps : post_spec) : bool :=
  match seg_run steps ss0 [] with Some (ss, w) => post_ok ps ss w | None => false end.

Lemma kn_word_entry : forall E M kn b k w v,
  know_ok segs E M kn -> kn_word kn b k w = Some v -> kentry_ok segs E M (KWord (SA b k) w v).
Proof.
  intros E M kn b k w v HK H. induction kn as [|K r IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hr]. cbn [kn_word] in H.
  destruct K as [[b' k'] w' v'| | | | | | | | |]; try exact (IH Hr H).
  destruct (expr_eqb b' b && Z.eqb k' k && Nat.eqb w' w)%bool eqn:Hc; [|exact (IH Hr H)].
  injection H as <-. apply andb_true_iff in Hc as [Hc Hw]. apply andb_true_iff in Hc as [Hb Hk].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Hk. apply Nat.eqb_eq in Hw. subst b' k' w'. exact HKK.
Qed.

Lemma region_flat_chk_sound : forall E M kn r,
  know_ok segs E M kn -> region_flat_chk kn r = true ->
  let '(rb, rlo, rlen) := r in 0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64.
Proof.
  intros E M kn [[rb rlo] rlen] HK H. unfold region_flat_chk in H.
  assert (GEN : (Z.ltb 0 rlen && existsb (fun K => match K with
                         | KWr (SA b lo) (ELit len) => (expr_eqb b rb && Z.leb lo rlo && Z.leb (rlo + rlen) (lo + len) && Z.ltb len two64 && Z.leb 0 len)%bool
                         | _ => false end) kn)%bool = true ->
                0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64).
  { intros G. apply andb_true_iff in G as [G0 G]. apply Z.ltb_lt in G0.
    apply existsb_exists in G as (K & Hin & HKc).
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    destruct K as [| | | | | |[b lo] [len| | | | | | |]| | |]; try discriminate.
    apply andb_true_iff in HKc as [HKc H0]. apply andb_true_iff in HKc as [HKc Hlt].
    apply andb_true_iff in HKc as [HKc H2]. apply andb_true_iff in HKc as [Hb H1].
    apply expr_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0. subst b.
    cbn [kentry_ok] in HKK. destruct HKK as [Hfl _]. unfold flat, elenZ in Hfl. cbn [edenot] in Hfl.
    rewrite u64_of_Z in Hfl by (unfold two64 in Hlt; lia). unfold two64 in Hlt.
    unfold estart in *. cbn [a_base a_off] in *. pose proof (bv_unsigned_in_range _ (edenot E rb)). lia. }
  destruct rb as [z| | | | | | |]; try (apply GEN; exact H).
  destruct z; try (apply GEN; exact H).
  apply andb_true_iff in H as [H H2]. apply andb_true_iff in H as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
Qed.

(* [comment removed for export] *)
Definition regions_ok (E : env) (F : list region) : Prop :=
  Forall (fun r : region => let '(rb, rlo, rlen) := r in
            0 <= estart E (SA rb rlo) /\ 0 < rlen < 2 ^ 64 /\ estart E (SA rb rlo) + rlen <= 2 ^ 64) F.
Lemma regions_ok_flat : forall E F, regions_ok E F -> regions_flat E F.
Proof.
  intros E F H. unfold regions_ok, regions_flat in *. eapply Forall_impl; [|exact H].
  intros [[rb rlo] rlen] X. lia.
Qed.

Theorem run_post_sound : forall (fx : FPState) steps pc0 sr0 kn0 nx0 ps E R M,
  Forall step_req steps ->
  run_post_ok steps (SS pc0 sr0 [] kn0 nx0) ps = true ->
  regs_ok E sr0 R -> know_ok segs E M kn0 ->
  exists (fx' : FPState) E' R' M' ,
       env_agree nx0 E E'
    /\ msteps segs (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom segs)) (@mkst fx' R' (Z_to_bv 64 (ps_pc ps)) M' (seg_rom segs))
    /\ (forall i e, In (i, e) (ps_regs ps) -> (0 < i < 32)%nat -> getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ regions_ok E' (ps_regions ps)
    /\ (forall a : word, outside E' (ps_regions ps) a -> M' a = M a)
    /\ know_ok segs E' M' (ps_cells ps)
    /\ mem_grows M M'.
Proof.
  intros fx steps pc0 sr0 kn0 nx0 ps E R M Hreq H HR HK. unfold run_post_ok in H.
  destruct (seg_run steps (SS pc0 sr0 [] kn0 nx0) []) as [[ss w]|] eqn:Hrun; [|discriminate].
  destruct (seg_run_sound fx steps (SS pc0 sr0 [] kn0 nx0) [] ss w E R M Hreq Hrun) as (fx' & E' & R' & Hag & _ & [HR' HK'] & Hcl & Hms).
  { split; [exact HR | cbn [wden]; exact HK]. }
  unfold post_ok in H. apply andb_true_iff in H as [H Hcells]. apply andb_true_iff in H as [H Hflat].
  apply andb_true_iff in H as [H Hw]. apply andb_true_iff in H as [Hpc Hregs].
  apply Z.eqb_eq in Hpc.
  exists fx', E', R', (wden E' M w). cbn [s_next s_pc wden] in *.
  assert (ROK : regions_ok E' (ps_regions ps)).
  { unfold regions_ok. apply Forall_forall. intros r Hin. rewrite forallb_forall in Hflat.
    exact (region_flat_chk_sound E' (wden E' M w) (s_know ss) r HK' (Hflat r Hin)). }
  split; [exact Hag|]. split; [rewrite <- Hpc; exact Hms|]. split; [|split; [|split; [exact ROK|split; [|split]]]].
  2:{ rewrite (HR' (Z_to_bv 5 0)). reflexivity. }
  - intros i e Hin Hi. rewrite forallb_forall in Hregs. specialize (Hregs (i, e) Hin). cbn [fst snd] in Hregs.
    apply expr_eqb_eq in Hregs. rewrite <- Hregs. rewrite (HR' (Z_to_bv 5 (Z.of_nat i))). unfold sr_get.
    replace (bv_eqb (Z_to_bv 5 (Z.of_nat i)) 0) with false.
    2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32%Z.
        rewrite Z.mod_small by lia. change (bv_unsigned (0%bv : bv 5)) with 0%Z. lia. }
    rewrite ridx_of_nat by lia. reflexivity.
  - intros a Ha. eapply wden_frame; [exact Hw | apply regions_ok_flat; exact ROK | exact Ha].
  - unfold know_ok. apply Forall_forall. intros K Hin. rewrite forallb_forall in Hcells. specialize (Hcells K Hin).
    apply existsb_exists in Hcells as (K' & Hin' & Heq). apply APS.kentry_eqb_eq in Heq. subst K'.
    exact (proj1 (Forall_forall _ _) HK' K Hin').
  - clear. induction w as [|g r IH]; cbn [wden]; [apply mem_grows_refl|].
    destruct g as [a0 wd v|db dk sb sk n|db dk n c].
    + eapply mem_grows_trans; [exact IH | apply wbytes_grows].
    + destruct (rdn segs (wden E' M r) _ _); [eapply mem_grows_trans; [exact IH | apply wbytes_grows] | exact IH].
    + eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

End WithSegs.
End SR.

End SegRun.
