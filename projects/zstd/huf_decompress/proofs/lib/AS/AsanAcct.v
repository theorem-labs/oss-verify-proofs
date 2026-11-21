(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (49 recorded proofs replaced by written proofs (fetch_failure_restrict, interp_eff_accesses_restrict, decode_exec_accesses_restrict and 46 more); P_silent1 takes the premise that no system call is pending). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import CatSim PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanAcct () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions@Z_to_bv_unsignedc59OSSVerify5KrLib2AS8AsanAcct4woffC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addK47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC45stdpp9bitvector;definitions?bv_add_unsignedC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2AS8AsanAcct<range_avoidsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08c59OSSVerify5KrLib2AS8AsanAcct6woff_0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega;ZifyClasses7rew_iffc59OSSVerify5KrLib2AS8AsanAcct9woff_succC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List2Inc59OSSVerify5KrLib2AS8AsanAcct<ranges_avoidC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic2or00C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9in_app_orC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_transI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcK47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memc59OSSVerify5KrLib2AS8AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct>asanreflect_fxC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityc59OSSVerify5KrLib2AS8AsanAcct8restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct:unrestrictC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01c59OSSVerify5KrLib2AS8AsanAcctEmunrestrict_mrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrc59OSSVerify5KrLib2AS8AsanAcctEmrestrict_munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib2AS8AsanAcctBhclean_restrict_idC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctCrestrict_unrestrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic3and01c59OSSVerify5KrLib2AS8AsanAcctCmemory_read1_hiddenC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indc59OSSVerify5KrLib2AS8AsanAcctArange_avoids_consC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI47Corelib4Init5Logic4True00C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc59OSSVerify5KrLib2AS8AsanAcct>wview_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib2AS8AsanAcct?range_avoids_hdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct?range_avoids_tlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctJov_read_bytes_mrestrict_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctBwview_mrestrict_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC47Corelib4Init5Logic3notC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith4Znat3N2Z9is_nonnegc59OSSVerify5KrLib2AS8AsanAcctFfind_segment_none_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAseg_ov_read_bytesC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c59OSSVerify5KrLib2AS8AsanAcctEin_segment_not_hiddenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executablec59OSSVerify5KrLib2AS8AsanAcctFfind_segment_some_specC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Znat7N_nat_Zc59OSSVerify5KrLib2AS8AsanAcctJseg_ov_read_bytes_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<code_read_ovC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4c59OSSVerify5KrLib2AS8AsanAcctEcode_read_ov_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_half_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_halfc59OSSVerify5KrLib2AS8AsanAcctFfetch_half_ov_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics5Riscv7Prelude4bitsC45stdpp9bitvector;definitions9bv_concatc59OSSVerify5KrLib2AS8AsanAcctGfetch_half_any_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyK47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC47Corelib4Init9Datatypes3orbK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureI47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c59OSSVerify5KrLib2AS8AsanAcct@ranges_avoid_nilC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics5Riscv3Sem3eff02K4ELinuxProcessSemantics5Riscv3Sem3eff03K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05K4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv3Sem3eff07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesc59OSSVerify5KrLib2AS8AsanAcctFov_read_bytes_restrictC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01c59OSSVerify5KrLib2AS8AsanAcctAranges_avoid_consC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff08c59OSSVerify5KrLib2AS8AsanAcctAstore_ok_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBaseDlength_Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib2AS8AsanAcctEwrite_to_mem_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctCwrite_to_mem_hiddenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7eff_indC45stdpp9bitvector;definitions:bv_extractI4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv3Sem3eff00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalK4ELinuxProcessSemantics5Riscv3Sem4core01c59OSSVerify5KrLib2AS8AsanAcct?restrict_hcleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctLinterp_eff_accesses_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4execI4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordc59OSSVerify5KrLib2AS8AsanAcct;restrict_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctFfetch_word_ov_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctGfetch_tail_any_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctFfetch_failure_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctMdecode_exec_accesses_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib2AS8AsanAcctFstep_accesses_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctIrestrict_unrestrict_cleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctCstep_restrict_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC56Stdlib6ZArith6BinInt1Z3mulI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib2AS8AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingI4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib2AS8AsanAcct4A_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct7A_pagesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc59OSSVerify5KrLib2AS8AsanAcct>Zmod0_multipleC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z<eq_decidableK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z6to_natK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:length_appC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapc59OSSVerify5KrLib2AS8AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC46Stdlib5Lists4List:in_map_iffI47Corelib4Init5Peano2le00C46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib5Lists4List9in_or_appC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC46Stdlib5Lists4List8map_consI46Stdlib5Lists4List5NoDup00K46Stdlib5Lists4List5NoDup01K46Stdlib5Lists4List5NoDup02C46Stdlib5Lists4List9NoDup_indc59OSSVerify5KrLib2AS8AsanAcctENoDup_map_bv_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct:A_pages_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC46Stdlib5Lists4ListANoDup_incl_lengthK46Stdlib9micromega:ZMicromega;ZArithProof03c59OSSVerify5KrLib2AS8AsanAcct>A_pages_lengthC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC57Corelib7BinNums6PosDef3Pos3mulC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_addC46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC46Stdlib;setoid_ring6Ncring>ring_mult_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2Zrc59OSSVerify5KrLib2AS8AsanAcct>two64_as_pagesC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib6ZArith4ZdivAZmult_mod_distr_lC4ELinuxProcessSemantics?LinuxProcessSem5State8page_memC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics?LinuxProcessSem5State;page_insertC4ELinuxProcessSemantics?LinuxProcessSem5State@access_pages_accc59OSSVerify5KrLib2AS8AsanAcctApage_insert_nodupC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesc59OSSVerify5KrLib2AS8AsanAcctFaccess_pages_acc_nodupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct>page_insert_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctCaccess_pages_acc_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateHnewly_materialized_pagesC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesc59OSSVerify5KrLib2AS8AsanAcctAaccesses_pages_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctDaccesses_pages_nodupC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<NoDup_filterc59OSSVerify5KrLib2AS8AsanAcctEpage_mem_false_not_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctDpage_base_of_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct>page_base_woffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib2AS8AsanAcctEm_vm_materialized_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct=m_vm_lazy_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct>eager_used_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct<m_vmmaps_wvbC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS8AsanAcct4MInv01C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS8AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc59OSSVerify5KrLib2AS8AsanAcct?new_pages_propsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9NoDup_appc59OSSVerify5KrLib2AS8AsanAcctCallowed_pages_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedc59OSSVerify5KrLib2AS8AsanAcct8MInv_wvbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctEvm_backing_used_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctFmaterialize_restrictedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib2AS8AsanAcctJmi_account_step_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct7node_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctDwith_vm_backing_sameC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg00K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg01C59OSSVerify5KrLib3Lib3Cfg<sstep_of_cfgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct?sstep_instr_detC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct;step_hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim:msteps_indC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctEnode_instr_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctJsame_but_materialized_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctCunrestrict_restrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctDrestrict_svc_pendingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctKsame_but_materialized_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctFunrestrict_munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct>unrestrict_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct=msteps_hcleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctDrz_msteps_restrictedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctBwith_vm_backing_idC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome00c59OSSVerify5KrLib2AS8AsanAcctAmaterialized_succC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9sstep_cfg04C4ELinuxProcessSemantics?LinuxProcessSem5StateIm_killed_of_m_halted_noneC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgc59OSSVerify5KrLib2AS8AsanAcct3mkHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctCpage_in_ranges_inclC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct@wx_segs_nowrap_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct7seg_topC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib2AS8AsanAcct>wx_segs_nowrapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct<segs_below_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctHfind_segment1_none_aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posc59OSSVerify5KrLib2AS8AsanAcct=ranges_from_bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct<page_base_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcct9mkH_aboveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS8AsanAcctDH_off_segments_aboveC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.

Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if H a then None else m a.

(* [comment removed for export] *)
Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
    : word -> option byte :=
  fun a => if H a then full a else m' a.

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := mrestrict H (ms_mem ms);
     ms_rom := ms_rom ms |}.

Definition unrestrict (H : word -> bool) (full : word -> option byte)
    (ms' : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
     ms_pc_val := ms_pc_val ms';
     ms_svc_pending := ms_svc_pending ms';
     ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
     ms_mem := munrestrict H full (ms_mem ms');
     ms_rom := ms_rom ms' |}.

(* [comment removed for export] *)
Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
  forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

(* [comment removed for export] *)
Definition wx_segs_nowrap (segs : list Segment) : Prop :=
  forall seg, In seg segs ->
    seg_executable seg && seg_writable seg = true ->
    (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.

(* [comment removed for export] *)
Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
  forall a n, In (a, n) l -> range_avoids H a n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h02b1h12b2h21nh31zh41Hh51ap;1p;3p;2p;6p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p8P0p1001Qp4p710p8P0p10022R1p4p710p8P0P1p4p7210p8P0p1002Op4p710p8g002kj13Tg003Pj1?Tg003nj12Tg004Qj30Tg004kj21Tg005Uj3<Tg0069j1;Tg006Yj24Tg0076j28Tg007\j25Tg008Bj27Tg0095j39Tg009aj1:Tg00:Bj66Tg00:`j2>Tg00;Oj2=Tg00<D#3#3#3#3#3#3#?R0#2R1g00<iR2f0R3#2R4f1R5#2R6g00=Gf2R7#2?053g00=bR8f3R9/17119530R:[11751173508%29?075[R;f4#2?097\:A<753P3n2001000000120000000W1W0W2P;^16^04^22P3P01105R2g00>@R4#;'4R6,80R;P5P815061107R79083X38P8P21503=087X3817059902g00>_,42%:2E6110;1>06E6O4b41=34=013eW5o"). Qed.

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01zh11xh21nh34__x1h44__x2h52b1h62b2h71Hh82H1h97__arithh:4__ffh;8__varmaph<5__with=1ah>4cstrh?1kh@1mhA1yp;1p;3p;2p;4p;<p;7p;8p;6p;Bg002kj16Tg003Pj1fTg003nj17Tg004Qj38j1XTg004kj21Tg005Uj3YTg00?=j1WTg00?[j3ATg00@>j3=Tg0069R0j14Tg006YR1j20Tg0076j2>Tg00@cR2j1<Tg007\j23Tg00ABj2\Tg00Aej1ZTg00BNR3j2;j1BTg00Bnj2?Tg00CHj1VTg00Cfj4UTg00DIl<QTg00Dnj1MTg00ESj2LTg00Eoj1KTg00FOj1JTg00Foj2ITg00GMj1NTg00Gkj4HTg00HIj1OTg00Hgj1PTg00IRj2@Tg00J5j2GTg00JXj3:Tg00K;j4eTg00Kfj7dTg00LJj2cTg00Llj2aTg00MXj3`Tg00N7j4_Tg00Nij4^Tg00OTj8DTg00P1j3]Tg00:Bj69Tg00PXj3[Tg00:`j2CTg00;Oj2ETg00QFl<FTg00QklBbTg00=bR4f1R5f0R638p=21?46p=5g00RQR7P7P4P4P2P0P0f3R2g00S0f2R8P5P6M<Fp=TP7P4P4P4P0P0f5R0f4R9P2P8P5P6M<Fp=SP4P4P4P4P4P4P1P6P5P8P1P2P9P0f6f7f8f9MBbp=Rg00<DR1#6R:#6#6#6#6#6#fR;#7R<g00<iR=%76R>%75R?g00=G%78?85611281125'2R@[11851186'2%72?885[RA%79?828\@AY856P6n2001000000120000000W6W5W2PA^6?^5>^2=P6P;%W1R=g00STR>5A;R?9=;8,1;RA%45'0R@,>;RB11;8RC%<5#4'0RD,>;REP413;@11;2RF%<8RG#4RH'0RI,>;,1;,26X04P413;DA=;2?,1;%48RJ'0,3;/26X04P411;?RK,0C,3;106J,3;13;IRC'2X04%5=P>1\;=d9A;=R>P<e,1;/2=P4P=11;9RL/06,3;%42'0,3;%<2#4,0LRL,3;'2X04P410F=R2/0JRM%Z;RN';1;LN,26X04P4P4%BM%BIPNPNP4P4\4RLP3P3PMPIPL\4/?312MI10J=R3,0FRL,2MP4P4%X4ROP6X14RPPO1256#VXA4X14PMPM%5MPIPLPPPPPPP4P4g00T01056CU#5X@4X24PFPF%5FPHP3PPPP%46#5X17PGP3106=R3X14P8PJ%5JCTESM:RM<Q%M8g00>_RG/LJg00TTRP#K%JPP41I48P5%N4CH%O4%P4RPg00U@g00U_RHPHg00V?RHP41@41R11G4=RF5:41@4:R:5:4g00V_A:4:F9:41Ceg00WFFd1cPHP6P8g00WfRHg00XFRP'?1a68=8HPdA`4G5C_b:b;b<X34X441035105=,06'2^34^44P6%4911;0O2b9b>C^GD%5NGD1;2N/0J/;NA]2JNE913;2/0J,3;/2CePKP6E9b8PAA[;8?E911;E1C;DE911;B1C;@E9O4b7A=;5>/E6%<6,E558<eX?7W=o"). Qed.

Lemma range_avoids_hd : forall H a n,
  range_avoids H a (S n) -> H a = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h04__x1h11ah21Hh32Hrh47__arithh54__ffh68__varmaph75__with84cstrh91nh:1xp;1p;3p;2p;4p;8p;6p;<p;7g002kj10Tg003Pj1VTg003nj1BTg00@cR0j19Tg00Xfj3UTg00;Oj2MTg004Qj37Tg00YcR1j2ATg0069R2j16Tg00?=j1?Tg006Yj21Tg00Z;R3j2:Tg00Bnj22Tg00Dnj1QTg00ESj28Tg00Eoj1LTg00FOj1KTg00Foj2FTg00HIj1ETg00Hgj1DTg00J5j24Tg00IRj2CTg00K;j43Tg00ZWj1@Tg00JXj3GTg00[9j8HTg00LJj2ITg00Llj2JTg00MXj3>Tg00N7j4=Tg00Nij4NTg00[]j1<Tg00\Tj6OTg00QFl<PTg00DIl<;Tg00Kfj7RTg00RQR4P4g00=bR5P5P0P2P2f3R0g00S0f2R6f1R7f0R8M<Pp=TP4P5P1P2P3g00]0g00>@R3g00>_R2P0P6P7P8M<;p=SP7g00U@R1g00U_R9P9g00V?R:P8g00WFFRp=5g00<DR;#0#0#0#0#0#0#V#BR<g00WfR=[%989U67P<1M63f4P8O1g00]R57=X1<P8P3%97R>,A3%67R3%?;R?'1R@,:21252P>P@118?X:5P7P31253CTCS%Q71823g00TTR3#L%K31F57%E5%D5R3P1P9P9P:P51452R1g00^21C5;R;C3,53%@9P5P1g00^Y145?9G5;C3,53GH1I3:P8P6g00XFR3,2=1J86=7=3dA>527C=b5b6b7X051828117?,:2[^05P8%60P7O2b4b8CNO2P6%<6EOW3X94X1<W2o"). Qed.

Lemma range_avoids_tl : forall H a n,
  range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h04__x1h14__x2h21Hh32Hkh43Hk0h52Hrh67__arithh74__ffh88__varmaph95__with:1ah;1bh<4cstrh=5cstr0h>1kh?1nh@1xp;1p;3p;2p;4p;8p;6p;<p;7g002kj10Tg003Pj1\Tg003nj1NTg00@cR0j16Tg00Xfj3ATg00YcR1j25Tg00;Oj2=Tg004Qj3<Tg0069R2j12Tg00?=j1HTg006Yj21Tg00Z;R3j23Tg00Bnj24Tg00_@j4VTg00Dnj1?Tg00ESj2>Tg00Eoj1UTg00FOj1TTg00Foj2STg00GMj1RTg00Gkj4MTg00HIj1LTg00Hgj1KTg00IRj2:Tg00K;j49Tg00ZWj1ITg00J5j2JTg00JXj37Tg00[9j8GTg00LJj2FTg00Llj2OTg00MXj3ETg00N7j4PTg00Nij4QTg00?[j38Tg00@>j3@Tg00_gj2DTg00:Bj6[Tg00ABj2ZTg00QFl<YTg00DIl<WTg00Kfj7XTg00RQR4P4g00=bR5P5P0P2P2f3R0g00S0f2R6f1R7f0R8M<Yp=CP4P5P1P2P3g00]0f5R3f4R2P0P6P7P8M<Wp=BP7g00U@R1g00U_R9P9g00V?R:P8g00WFFXp=;g00<DR;#0R<#0#0#0#0#0#\R=#NR>g00WfR?[%689A671586P>%67R@,=2f6P8O1g00]R5<?X;>P6P@%60RA,5@%27RB%H;RC'1RD%20RE/1CRF'3P@PD118CX@5RDP7PB145BR@CCPAPFPDP0PE145ERDCCEB157013BERFP7PBP@P0PEPDEBP8CVPF%?6g00>_RF%26'>%?3%23R3,>Fg00TTRD#U%TDP51S56P7%R5CM%L5%K5RDP1P9P9P:P51:5;R;g00^YR11:5<R<C9,;D%I9P51J5CR9975;P1A75<9C9,;DGG1FD:P8P6g00XFRD,4?1O86=<?DdAE5F7CPb7b8b9X05X151387117C116C'3[^05^15P8f7#2P3P0O3b6b=b<b4CQO2g00STR398=C9@=2/=71D27E[W3X>4P31Z=Cd98=C9@=6=A07eW5X?4X:>W2o"). Qed.

Lemma range_avoids_cons : forall H a n,
  H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h02Hkh14__x1h24__x2h31bh41kh51xh61Hh72H0h83Hk0h92Hrh:7__arithh;4__ffh<8__varmaph=5__with>1ah?4cstrh@5cstr0hA1ni001np;1p;2p;3p;6p;4p;8p;<p;7g002kj13Tg003Pj1_Tg003nj1OTg00?=j1^Tg00ABj2TTg00?[j3ATg00@>j3<Tg00Xfj3;Tg00@cR0j10Tg00YcR1j21Tg00;Oj26Tg00[]j1ETg00:Bj6]Tg0069R2j12Tg00Z;R3j27Tg00Bnj28Tg006Yj24Tg00_@j4PTg00Dnj1BTg00ESj2=Tg00Eoj1NTg00FOj1MTg00Foj2LTg00GMj1KTg00Gkj4JTg00HIj1HTg00Hgj1ITg00IRj2:Tg00J5j2GTg00JXj39Tg00K;j4CTg00ZWj1FTg00[9j8QTg00LJj2RTg00Llj2STg004Qj3DTg00MXj3\Tg00N7j4[Tg00Nij4YTg00_gj2VTg00\Tj6WTg00DIl<XTg00QFl<UTg00Kfj7ZTg00WfR4f0R5g00]R3Dp=5g00RQR6g00=bR7P1P2P3g00]0f5R3f4R1f3R8f2R9f1R:P5M<Xp=?P6P6P7P7P0P2P2P8g00S0P9P:P5M<Up=>P:g00U@R2g00U_R0P0g00V?R;P5g00WFFZp=@g00<DR<#3R=#3#3#3#3#3#_R>#OR?P4]5P9P:O1#5%^<R@g00STRA1T>@d5A>9<>9=;8:%08,15P6%03,15f8RBf7RC/6:O1#5]0P:g00>@RD%01'1P?f6REPBP5O1#5X3?P116ED%EEE]W0%05%0E'1P?AA>@A9<>B/6:f:P5O1#5X3?P3P:11:C%2:R>%2CRA'7P:P>187>REPCPA187ARDE?%0:RF%0CRG'114>@14A@'7RHPF145@RIX57RJP>O1PJP:P>PEC>PGPJPAO1PJPCPAPDC>E?P5CPPH%B9g00>_RH%29'=f9RD#B%2D,=Hg00TTRD#N%MDP71L79P:%K7CJ%H7%I7RDP2P0P0P;P71:7<R<1G7@R2597g00^YRA1:7=R==972CC,@D%F0P7P<PAP=CC,@DGQ1RD;P5P9g00XFRD,841S59=D4DdA\7H:C[b;b<b=X17X2714:@,7I17:9[^17^27P5f;#2%23P8O3b:b@b?b8CYO216BF1VB:EWW0X46P5O1n0110000020011100P5O1W0X46%099;18eW9W7XA6X>?W6o"). Qed.

Lemma ranges_avoid_nil : forall H, ranges_avoid H [].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh13Hinh21ah31np;1p;2p;4p;3g002kj10Tg003Pj18Tg003nj12Tg00`aj21Tg00aAj47Tg00Eoj16Tg00aaj33Tg00Xfj34Tg00b8j25Tg00<D#0#0#0#0#0#0#8#2R0g00Wf[g00RQR11101R2P0P1f1f0R1C7%62R233g00c5f4f3f234P1n010000000W1W3X201512eW0o"). Qed.

Lemma ranges_avoid_cons : forall H a n l,
  range_avoids H a n -> ranges_avoid H l -> ranges_avoid H ((a, n) :: l).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h02H0h12a'h21eh32n'h41Hh52Hah63Heqh73Hinh82Hlh91ah:1lh;1ni001ni011bi021pp;1p;2p;3p;6p;4g002kj12Tg003Pj1=Tg003nj1:Tg00`aR0j29Tg00FOj1<Tg00Xfj33Tg00b8j28Tg00cRj35Tg00aaj34Tg004Qj31Tg00d2j66Tg00\Tj67Tg00aAj4;Tf2R1g00RQR2f1R3f0R4C;p=0g00<D#2#2#2#2#2#2#=#:R5g00Wf[1952R6#<f3R7?313f4R8/83A0534f6R9f5R:505=568546g00dOf7R;=059A0513R<516A46<:f9R<?371P4f8R==05;A0571R>516P6P2P0P5P2P2P4P4n2001102000120101100X26A05<=A0587R?P4E6A12=7P6P5P0P5P2P5P4P3n2001102000120101100X26f:R0=05<A05:8P3E6A150:f;R<=159P5f<R@A12@;f?RA?33=[X15A12<9P2P@f>=3A4X32P0P;P4E7W0P;P4E7W0P4O1b0P4O1b0W6P4O1A46>9P:P8P7P4O3W7P4O1n200100000021100010000W0X32X15A56?1,8:eW8W5W:X;2X95W4o"). Qed.

Lemma ranges_avoid_app : forall H l1 l2,
  ranges_avoid H l1 -> ranges_avoid H l2 -> ranges_avoid H (l1 ++ l2).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h03Hinh11Hh22H1h32H2h41ah52l1h62l2h71np;1p;2p;4p;3p;5g002kj11Tg003Pj1;Tg003nj16Tg00`aj25Tg00FOj1:Tg00b8j23Tg00aAj42Tg00dij34Tg00aaj30Tg00eFj57Tg00dOR0j28Tg00Xfj39Tg00<D#1#1#1#1#1#1#;#6R1g00Wf[g00RQR2,51R3#:R4f2R5f1R6'3f3R7/36P1P2P6f0R8C2f5R9f4R:543503P3f6R;P9P1P2P5P6C2R6P8D7A036;A0369'8P0P1P2P7P5C2R0f7R6503A030;f9?9:7P8P1P2P:P7C2R0f8503P6P9P:P8O3W0P8O1A0306P;P9P:P8O3W0P8O1n200100000021000010000b0W0X72X41A4375,3:eW3W2X64W5W1o"). Qed.

(* [comment removed for export] *)
Lemma restrict_svc_pending : forall H ms,
  ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12msp;1p;2p100edp4p7210R0g00BnR1p4p710p8P0p100\Tp4p710p8P0p100fPp4p710p8P0p100d2p4p7210p8P0p100OTp4p7210p8P0p100:Bp4p710p8P0p100fnp4p710p8g002kj10Tg003Pj15Tg003nj12Tg00h5j11Tg00hWj14TP1j23Tg00<D#0#0#0#0#0#0#5#2R1g00Wf[g00i]%11f0#4'3W1W0o"). Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12msp;1p;2g002kj10Tg003Pj14Tg003nj12Tg00jdj11Tg00Bnj23Tg00<D#0#0#0#0#0#0#4#2R0g00Wf[g00i]f0#1,30W1W0o"). Qed.
Lemma restrict_regs : forall H ms, ms_regs (restrict H ms) = ms_regs ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12msp;1p;2g002kj10Tg003Pj11Tg003nj13Tg00kaj12Tg00edj26Tg00lFj15Tg00Bnj24Tg00<D#0R0#0#0#0#0#0#1#3R1g00Wf[g00i]%20#1/61f0#5'4W1W0o"). Qed.
Lemma restrict_reg : forall H ms r, ms_reg (restrict H ms) r = ms_reg ms r.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12msh21rp;1p;2g002kj10Tg003Pj12Tg003nj11Tg00kaj13Tg00mEj25Tg00Bnj24Tg00<D#0R0#0#0#0#0#0#2#1R1g00Wf[g00i]%30#2#1f1f0'5,41W2W1W0o"). Qed.
Lemma restrict_rom : forall H ms, ms_rom (restrict H ms) = ms_rom ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12msp;1p;2g002kj10Tg003Pj12Tg003nj11Tg00h5j13Tg00nCj15Tg00Bnj24Tg00<D#0#0#0R0#0#0#0#2#1R1g00Wf[g00i]%20#1#3\1f0#5'4W1W0o"). Qed.
Lemma restrict_mem : forall H ms, ms_mem (restrict H ms) = mrestrict H (ms_mem ms).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12msp;1p;2g002kj10Tg003Pj12Tg003nj11Tg00h5j13Tg00oAj16Tg010?j25Tg00Bnj24Tg00<D#0#0#0R0#0#0#0#2#1R1g00Wf[g00i]%20#1#3\1f1f0#6'5'4W1W0o"). Qed.
Lemma unrestrict_svc_pending : forall H full ms,
  ms_svc_pending (unrestrict H full ms) = ms_svc_pending ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh14fullh22msp;1p;2g002kj10Tg003Pj13Tg003nj12Tg00h5j11Tg00hWj15Tg00Bnj24Tg00<D#0#0#0R0#0#0#0#3#2R1g00Wf[%30#2#1\1g00i]%11f0#5'4W2W1W0o"). Qed.
Lemma unrestrict_mem : forall H full ms,
  ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh14fullh22msp;1p;3p;2g002kj10Tg003Pj12Tg003nj11Tg00h5j13Tg00oAj16Tg0119j35Tg00Bnj24Tg00<D#0#0#0R0#0#0#0#2#1R1g00Wf[%20#1#3\1R1g00i]f2f1f0#635,41W2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma restrict_mkst : forall H regs pc mem rom,
  restrict H (mkst regs pc mem rom) = mkst regs pc (mrestrict H mem) rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh13memh22pch34regsh43romp;1p;2p;5p10125p4p70R0p100\Tp4p710R1p8P0p100fPp4p710R2p8P0p100d2p4p7210R3p8P0p100:Bp4p710R0p8p1012ep4p70R4P1p8P4P2p8P4P3p8P4P0p8P4p100dip4p710p8p1013Sp4p70R4P1p8P4P2p8P4P3p8P4P0p8g002kj10Tg003Pj11Tg003nj12Tg00kaj13Tg00edj28Tg00h5j17Tg010?j26Tg014Ij54Tg00Bnj25Tg00<D#0R0#0#0R4#0#0#0#1#2R3g00Wf[%30#1/83%14#2#7\3R4g00i]g015>f3f2f4f1'6f0D4'5X44W1X23W3W0o"). Qed.

Lemma mrestrict_idem : forall H m, mrestrict H (mrestrict H m) = mrestrict H m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h01Hh11ah21bi001bh31mp;1p;2p;3p;5g002kj10Tg003Pj16Tg003nj14Tg00h5j17Tg010?j21j32Tg00ZWj19Tg004Qj35Tg00Bnj23Tg016=j58Tg00<D#0#0#0R0#0#0#0#6#4R1g00WfR2[%60#4R0#7R3\1P1P3f1R4f0R5,14R6'1P6f2R6P5O1P2P2P2P3P5%90R0P2P3P5P0f3P6O1n0100000020000R2n0100000020000=532P51330P6P4O1,33n0110000020000b21164=265A2645553eX11D8W3W0o"). Qed.

Lemma munrestrict_mrestrict : forall H m,
  munrestrict H m (mrestrict H m) = m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h01Hh11ah21bi001bh31mp;1p;2p;3p;4p;5g002kj10Tg003Pj12Tg003nj13Tg00h5j15Tg010?j24Tg0119j3:j47Tg00ZWj19Tg004Qj31Tg00Bnj26Tg016=j58Tg00<D#0#0#0R0#0#0#0#2#3R1g00WfR2[%20#3R0#5R3\1P1P3f1R4f0R514453:P5f2R6P5O1P2P2P2P3P5f3P6O1R7P2P3P5%90P7n0100000020000n0100000020000=137P5P6P4O1,63R7P7n0110000020000b2P6P41464P5C7P4P5O1513eX11D8W3W0o"). Qed.

Lemma mrestrict_munrestrict : forall H full m,
  mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h01Hh11ah21bi001bh34fullh41mp;1p;3p;2p;5g002kj10Tg003Pj13Tg003nj12Tg00h5j19Tg0119j37Tg010?j26j31Tg00ZWj1:Tg004Qj34Tg00Bnj25Tg016=j58Tg00<D#0#0#0R0#0#0#0#3#2R1g00WfR2[%30#2R0#9R3\1R4P1P3f2R5f1R6f0R7575'61657f3R8P7O1P2P2P2P3P7%:0R0P2P3P7f4P5O1P8P5O1R9n0100000020000n0100000020000P2P3P7P0P9n0100000020000543P71530P5P6O1,53n0110000020000b2A7856=187A1867543eX11D8X44W3W0o"). Qed.

Lemma unrestrict_restrict : forall H ms,
  unrestrict H (ms_mem ms) (restrict H ms) = ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h01Hh12msh27ms_fcsri007ms_fcsrh38ms_fregsi018ms_fregsh46ms_memi026ms_memh59ms_pc_vali039ms_pc_valh67ms_regsi047ms_regsh77ms_resvi057ms_resvh86ms_romi066ms_romh9>ms_svc_pendingi07>ms_svc_pendingh:1oi081mp;1p;2p;3p;8p;6g002kj10Tg003Pj12Tg003nj15Tg00oAj14Tg017?j2@Tg0188j3<Tg004Qj33Tg00kaj1DTg00edj2CTg00h5j17Tg0193j81Tg00Bnj2BTg010?j26Tg0119j3ATg01::j2FTg00:Bj6ETg00lFj1=Tg01;@j1>Tg01<@j1?Tg00hWj1;Tg01=Aj19Tg01>@j18Tg00nCj1:Tg00<D#0R0#0#0R1#0#0R2#0#2#5R3g00Wf[g00i]R4P4f2R5f0R6#41@563<=346P6%D0#2/C3R0%73R7%22#5%21#5#7\3R1P1f1R2f8R8f7R9f6R:f5R;f4R<f3R=P6P2G1P8P9P:P;P<P=P5P2G1534X:1P9P:P;P<P=P5P2P6G1R8,B4fAR>16>27A21F>2EE%=8%>8%?8%;8%98%88%48R?,6>%:8G1R@#=%>@%?@%;@%9@%8@%4@9A>?%:@G1=348e1@>89<>?=348eX81W4W2X77W9X53X30W6P9P:P;P<P=P5P2P6O8n01108000181104101103107105100102106W1W0o"). Qed.

Lemma restrict_unrestrict : forall H full ms,
  restrict H (unrestrict H full ms) = restrict H ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h01Hh14fullh22msh37ms_fcsri007ms_fcsrh48ms_fregsi018ms_fregsh56ms_memi026ms_memh69ms_pc_vali039ms_pc_valh77ms_regsi047ms_regsh87ms_resvi057ms_resvh96ms_romi066ms_romh:>ms_svc_pendingi07>ms_svc_pendingh;1oi081mp;1p;3p;2p;8p;6g002kj11Tg003Pj14Tg003nj16Tg00h5j17Tg0188j3ATg017?j25Tg004Qj33Tg00kaj1DTg00edj2CTg010?j22Tg0193j80Tg00Bnj2BTg0119j39Tg01??j3FTg00:Bj6ETg00lFj1@Tg01;@j1=Tg01<@j1>Tg00hWj1?Tg01=Aj1<Tg01>@j1:Tg00oAj18Tg00nCj1;Tg00<D#1R0#1#1R1#1#1R2#1#4#6R3g00Wf[%41#6#7\3R1g00i]R4P4f3R5f2R6f0R75A5'51557534P7%D0#4/C3R0%73R8%42#6P1fBR2f1R9'2R:f8R;f7R<f6R=f5R>f4R?P5P7P9G0P;P<P=P>P?P5fC/26P9G0534X;1P<P=P>P?P5P6P:P7G0,B4fAR:=929,22AF2:9EEP<P=P>P?P5P6P9P7G0R;#@R@%=;RA%>;RB%?;RC%<;RD%:;RE%8;RF992:%;;RGG0RH#@%=H%>H%?H%<H%:H%8H,22%;HG0P@PAPBPCPDPE122FPGG0534eAA2:;,52152;534eX91X51W3X88W:X63X40W7P<P=P>P?P5P6P9P7O8n01108000181104101103107105100102106W2W1W0o"). Qed.

(* [comment removed for export] *)
Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
  forall a, H a = true -> ms_mem ms a = None.

Lemma restrict_hclean : forall H ms, hclean H (restrict H ms).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12Hah21ah31bh42msp;1p;3p;2p;6g002kj10Tg003Pj15Tg003nj12Tg004Qj31Tg00h5j1<Tg00ZWj1;Tg00oAj23j17Tg00Bnj29Tg00:Bj68Tg010?j36Tg017?j24Tg01@Ej2:Tg00<D#0#0#0R0#0#0#0#5#2R1g00WfR2[g00i]f2R3f0R4O1g00XFR5512P2P5%50#2R0#<R5P2P5P4%;0R0f3R6/33n0100000020000;10X321950P6f1R2O1P4E8%73=662=150e1463/32=150eW1X211424,:2eW4W0o"). Qed.

Lemma hclean_restrict_id : forall H ms, hclean H ms -> restrict H ms = ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "p'0h01Eh12Hch21Hh31ah41bi001bh52msh67ms_fcsri017ms_fcsrh78ms_fregsi028ms_fregsh86ms_memi036ms_memh99ms_pc_vali049ms_pc_valh:7ms_regsi057ms_regsh;7ms_resvi067ms_resvh<6ms_romi076ms_romh=>ms_svc_pendingi08>ms_svc_pendingi091mp;1p;2p;3p;8p;7p;6p;4p;5g002kj11Tg003Pj12Tg003nj16Tg01@Ej25Tg017?j2;Tg004Qj30Tg00kaj1CTg00edj2?Tg00h5j1:Tg0193j84j78j6<Tg010?j27j3HTg00Bnj23Tg00ZWj1JTg01A<j4ITg016=j5GTg00OTj89Tg00lFj1BTg01;@j1@Tg01<@j1ATg00hWj1>Tg01=Aj1DTg01>@j1ETg00oAj1=Tg00nCj1FTg00<D#1R0#1#1R1#1#1R2#1#2#6R3g00WfR4[g00i]R5f1R6f0R7'5P5f3R8/57f4R9/;6=056]1P6%C0#2/?3R0%:3R:%22#6%21#6R1#:R2\3R;fBf7R<f6R=f5R>P9P8f2R?P6P7G4'5P;P5f8R@P<P=P>P9P8fCRA/7?RBF8P@P<P=P>P9P8P?F8P6P6P;P5\;RCP@P<P=P>P9P8E<RDPDPBP?PC\;/3DP3P2PBP?fDRBP7O1P41347fEP6O1=047P4fGP8O1=047P4P2P6%J1R1P<P9O1RDn0100000020000=02D]0P6fFP?O1RDg00XF504P2P=P8O1RCP1P9P8P7O2CIW0g00]R904D132CW0n0110000020000P7O1b0b4AHB87P8P7O1502eX33DGG913;6G9P@P<P=P>P9P8P?P6G4R@#B%@@%A@%>@%D@%E@%=@,7A%F@G4=05@e1;A@=05@eW1X<;W8W6X;:W=X93X70W:P<P=P>P9P8P?P6P7O8n01109000181105102104108106101103107P7O1W1W5W2o"). Qed.

Lemma restrict_unrestrict_clean : forall H full ms,
  hclean H ms -> restrict H (unrestrict H full ms) = ms.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Hh12Hch24fullh31mh42msp;1p;2p;3p;6g002kj10Tg003Pj13Tg003nj12Tg00h5j14Tg01@Ej2:Tg017?j21Tg004Qj39Tg01AXj35Tg0188j36Tg01B[j37Tg00:Bj68Tg00<D#0#0#0R0#0#0#0#3#2R1g00Wf[%30#2#4\1g00i]R1f2R0f0R2':P1f3R3f1R4'1A9120X31A5342A6304,13A7304E8W1W4W2W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma memory_read1_hidden : forall a, H a = true -> memory_read segs a 1 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02Hah11ah21oi003segi011xp;1p;3p;2p;6g002kj10Tg003Pj13Tg003nj17Tg004Qj31Tg00h5R0j1:Tg00ZWj18Tg00FOj1?Tg01C_j1>Tg01Daj1=Tg004kj22Tg01E`j1<Tg01F^j14Tg01G<j29Tg01GYj1;Tg01H7j1DTg01HWj35Tg00Bnj2CTg00?=j1BTg01Iaj36Tg00:Bj6@Tg01Jej3ATg00<DR1#0#0#0R2#0#0#0#3R3#7g00WfR4p,1Hf0R5O1g00XF31g01KhR6#:R7%86%32#7#?R2#:R8P0P6P8P5P4P8%>5R9%=5R:f3,23%<5#4R;'9#;%31R<#DR=35%82R2n0100000020000P2n10110100021010000;12X271C82p,4segsR7f1R>,23R?%B136p,2HHP>P5O2E@P0P6P8%4<967?P4P8P9f2,23/9;#;=5:=P2n0100000020000P2n10110100021010000=182eAA7><=182eW0W1o"). Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
  ov_read_bytes segs (mrestrict H m) a n = Some bs ->
  ov_read_bytes segs m a n = Some bs /\ range_avoids H a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02Hrh12Hah25Hresth31mh41oi001oh52H0h61ah72bsh81nh94__p1h:4__x1h;1bi011bh<3Havh=5Hfullh>2Hkh?3Hk0h@2IHhA7__arithhB4__ffhC8__varmaphD5__withE2a0hF4cstrhG1ehH1khI4resti024resti031li042l0i051xp;1p;2p;4p;3p;6p;5p;<p;7p;8g002kj18Tg003Pj1ATg003nj1KTg00h5R0j1FTg00FOR1j1OTg010?j29Tg01Lgj20Tg01MIj43Tg00Eoj1GTg004Qj31Tg00Xfj3:Tg00YcR2j2PTg0069R3j1DTg00Z;R4j2MTg00Bnj2<Tg00_@j4]Tg00Dnj1\Tg00ESj2LTg00Foj2[Tg00HIj1ZTg00Hgj1YTg00J5j2XTg00IRj2WTg00K;j4JTg00ZWj1@Tg01NNj6VTg00LJj2UTg00Llj2TTg00MXj3STg00N7j4RTg00;Oj2QTg01O2j4ETg00@cj15Tg01Jej3=Tg00?=j1gTg00?[j3fTg00@>j32Tg00cRj37Tg01OMj2eTg00\Tj6>Tg01PQj2BTg01Q0j5aTg00:Bj6`Tg01R2j4_Tg00=GR5j2NTg00DIl<bTg00Kfj7cTg00[9j8dTf5R6f4R7f3R8f2R9f1R:C3f0R;31p=4A1678A:9:;'Np=6g00RQR<g00=bR=P2P3P4g00]0P8P9P:g00>@R4g00>_R3P;M<bp=^P:g00U@R2g00U_R>P>g00V?R?P;g00WFFcp=IP8P2P>P>P?P9P:P;Gdp=HA189:/N;p=?P71989P:P;C3p=;P6P7A289:P;C3p=Cg00<DR@#8#8#8RA#8#8#8#ARB#KRC%AA#KRA#FRD[RE%OARF%FFRGp,4segsRHp,1HRI/99RJP:P810F;RKE4PGPHP8P9P7C310F:RLPIP9P7E6[]7^6C]3RMX8<PGPHPJP:P4PKE4%GA,0F=1GLA:I94RNP;1P;41P:4%D:RO/M3RPP:PO1<=O1<=3C^P;C]PP%\9%D9,L3f7RPf6ROO1RQPDp-0RRg00TTRS#G%OS1[=:%Z=%Y=RSP=1X=3RTg00^21W=@RUCJ,IS%@>RVPSP=PUg00^YPTCJ,ISPVPSP2P>P>P?P8EVCHCH1US?P;P9g00WfRSg00XFR?'<1T;9=1S?dAS=3:CRbBbCbDX:=W91L3;1M:3P8[[^:=^9RP;PIf8R=/Q6O1g00]RR351S%D6P9P8O4bAb3bFb?W>XH<PNeCEPGPHP8P9P4C3PLPNC?eW0X7FX6CX3EPGPHPJP:%57PKE4PIP9O1PS1<S;PIP8O1=1S;PSPIP6O1=1S;P0PAPGP0PAPDPSPDP:%@ARJPQn010000002000010A;RNP0PFPD%A@R49=HOR>P1PAPDP;PJ10A:n10110300020020101104R1PJn10110500021010300R2n10110500021010100P0PFPGPHPIP=%g@g00STR@5fBRV92BPf:RTD;A7A:;,0FRU%@FRWn10110500021010200PWn1011050002101010010F6RX51GPGP0PAPGP0PAPDP=PPO1PNP0PFPDA=HP4P1PJn10110500021010300n10110500021010100P0PFPGPHf9RYA2B=VRZf;R[C3PUPWn10110500021010200PWn1011050002101010010FOR\PIPP%5TE6]0]1P:PIP7O1R]=1S?P0PAPGP0PFPDA=H64P1PJn10110500021010300R?P0PFPGPHPIPPA2BOVPYD;PUPWn10110500021010200R^PWn1011050002101010010F7R751GPGP>P0PAPGP0PFPDP;P1PJn10110500021010300P0PFPGPHPIPYPZP[D;PUPWn10110500021010200PWn10110500021010100=1G\X4GP;PW1eO:E>A1GWXPGPWP0PFPRP;g00c5RRg01RSn10110000021000000XGGRZP@P\P;E>PRPGP0PAPGP0PAPDPYP=O1PNP0PFPDA=H=4P1PJn10110500021010300n10110500021010100P0PFPGPHPTA2BYVRJf<R1C3PUPWn10110500021010200PWn1011050002101010010FPR4PIP=%5[E6/B;b5b0W0W1A1S]3P0PAPGP0PAPDPOP6O1PNP?n10110500021010100P^PWn10110500021010100=1G7P0PAPDPQPNP2n10110500021010100PDP0PAP0PAPGP;P0PFPGPHPIPTPJP1D;PUPWn10110500021010200RJPWn10110500021010100=1G4PGP0PAPGP:P0PFPGPHP[A2BTVRDf=R2C3PUPWn10110500021010200PWn1011050002101010010F=R=%519:IYRYC?]0P;A1GJ=PHPIP[PDP2D;PG1<G;PGPH19I1A2B[Vf>R[P;E4P0PFPGPH19I[A2B2Vf@RDP;E4P0PFPGP:A7AO;,0FPWn1011050002101020010F2RJ51GPGP0PFPGPHPDPBf?RUPVfBRNECA7AP;,0FPWn1011050002101020010F[RQPIPU%5NE6R7]0]2P:PGPH19IUA2B[VfAR^PKE4A7AO:,0F=1GQPNP^A2BDVRQP9P:O4PGPHP^PQfCROC310F9PIPQPOE6P5PGPHPNA2B^VR5fDRQ10F8E4A:I5QPGP0PFPGPHPOPBPNPVfER5ECA7AT;,0FPWn1011050002101020010F^PIPN%55E6P;PGPHPQA2BOVfFROPXE4A2BQVfG5:IPGP4PGP0PFPGP;A7A[;,0FPWn1011050002101020010F5PIPOfI#5E6X4GA7A1P,0F10FQ51GfHRQ#59:I5P6PIP5PQPDP;DaCEPHPOPBP5PVPQECP:E`W<W=P:P;O2n2001000000121000000bEW0W2XIFP;O1PGPH19I2A2B1VPUPWE410F191GWPGPWPZP@PJP;E>PR1B7;b5W0W2n10110001021110301P;P9O2b2b4W0X;AP;O1A1GW\PGPWPZP@P4P;E>PRPGPWP=PYC?/B;b5W0n10110001021110100P:O1b4W0W1n0110101020101P;P9O2b1b;PGPHP8P9%56R6C3PLPIP9P6E6eW0X7FX6CX3EX@MX8<P;C_X8<o"). Qed.

Lemma wview_restrict : forall m a,
  wview segs (mrestrict H m) a =
    if H a then None else wview segs m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02Hah11ah21bi001bh31mh41oi013segi021xp;1p;2p;3p;6g002kj11Tg003Pj1<Tg003nj16Tg00h5R0j18Tg00Bnj23Tg004Qj30Tg00ZWj19Tg01Lgj2@Tg004kj22Tg00?=j1?Tg01Iaj34Tg01Roj1>Tg01Daj1=Tg01E`j1DTg01F^j1CTg01G<j2;Tg01GYj1:Tg01T1j27Tg00:Bj6BTg010?j2ATg01U8j35Tg00<DR1#1#1#1R2#1#1#1#<R3#6R4%<2#6R2#8R5[p,1HR6f0R7O1R8g00WfR91397P6f1R:O1=097P9P6f3R;O1=097P0P2P5P9P5P:%92R<f5R=f4R>O1R?n01000000200001@27R@P0g01KhRAP5p,4segsRB123>RC%?1R134P9P5%>7RD%=7RE123=%D7#CR=';#:'7P<n0100000020000RFP<n10110200021010100RGn10110200021010000P9P5P:P<P0P2P5P?P@PGn10110200021010000n0100000020000505]0P:P6f2O1RGg00XF509%8AR?%9AP0PAP5P7PFP<n10110200021010100=05<X4?135<123;=4B1R1p,2HHP;P7O2EBW0g00]R909GP0P2P5P>P;O1P@P0PAP5P1P9P5PD1;C=#:,7EP<n0100000020000P<n10110200021010100n10110200021010000,35W0n0110001020000P7O1b0b21A6:=5B7P9P5P8P<A5B:7n0100000020000505eX14W3o"). Qed.

Lemma store_ok_restrict : forall n m a,
  store_ok segs (mrestrict H m) a n = true ->
  store_ok segs m a n = true /\ range_avoids H a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02Hsh12Hah21ah31mh41nh52H0h64__p1h74__x1h81bi001bh91oi011oh:3Havh;5Hfullh<2Hkh=3Hk0h>2IHh?7__arithh@4__ffhA8__varmaphB5__withC2a0hD4cstrhE1ehF1ki021xp;1p;2p;3p;4p;6p;5p;<p;7p;8g002kj18Tg003Pj1ITg003nj1CTg00h5R0j1LTg010?j24Tg00Xfj31Tg00=GR1j26Tg00Bnj2;Tg00YcR2j2@Tg0069R3j1<Tg00Z;R4j2?Tg00_@j4bTg00Dnj1`Tg00ESj2FTg00Eoj1[Tg00FOj1YTg00Foj2XTg00HIj1WTg00Hgj1VTg00J5j2UTg00IRj2RTg00K;j4BTg00ZWj1ATg01NNj6QTg00LJj2PTg00Llj2OTg00MXj3KTg00N7j4MTg00;Oj2NTg004Qj33Tg01O2j4ETg00@cj19Tg01U8j3:Tg00?=j1STg00?[j3TTg01V5j2aTg00\Tj6HTg01PQj2GTg00@>j35Tg01W4j4=Tg01Q0j5_Tg01R2j4^Tg00DIl<\Tg00Kfj7ZTg00[9j8]Tg00WfR5f3R6f2R7f1R8f0R9C=g00XFR:33p=2g00RQR;g00=bR<P2P3P4g00]0P6P7P8g00>@R4g00>_R3P9M<\p=JP8g00U@R2g00U_R=P=g00V?R>P9g00WFFZp=DP6P2P=P=P>P7P8P9G]p=>A359:p=0f5R?f4R@A5678P9C=p=7g00<DRA#8#8#8RB#8#8#8#IRC#CRD%IB#CRB#LRE[RFp,4segsRGp,1HRH/48RIP9P7C2PGP7P8P6C2A1H86'6[^2D]3RJX4;PGPIP9P4C2PGP7P8P4C2A1H84RK1;5:RL1@941@84%<8R4/?3RMP8P41;<41;<3CJP9CbPM%`7%<7,F3p-0RMg00TTR4#[%Y41X<8%W<%V<R4P<1U<3RNg00^21R<AROCB,D4%A=RPP4P<POg00^YPNCB,D4PPP4P2P=P=P>P6EQC>C>1P4>P9P7PL1O97#0dAK<38CMb@bAbBX7<W61F391?83P6[[^7<^6MP9PHf6R</N@O1g00]RR3535%<@P8P7O4b?bDb=W<XF;PKeCEW0X2DX3FPGPIP9%96C2PE14H7=:G8P0PBP5P9PG14H@PCP6%SAg00STRA5TCRIP<E7P3n10110200021010000#0X9EP9P5PEPHP8O1%ABRKA:G78n0100000020000RL1a78EHP0PBP5PLPG14H6PCP7PIP?E7P3n10110200021010000#0PHP7O1P51;59PHP6O1=359P5PHP?O1=359P0PBP5P5PEP8PKf7RK=:G<R6n0100000020000PGf8RL,4HPCPKPIf:R4E7P3n10110200021010000#0P0PBP5A:GLKPGf9R>PCPLPIf;RLE7P3n10110200021010000#0%9491HK'6R=]0]1P8PHP@O1R2#0A353:RPP5P3P5PMP9g00c5RMg01RSn0110000020000XE5PAP:P9EHR:PM1G=9b5W0W1A3523P0PBP5A:G<?PG14HKPCP<PIP>E7P3n10110200021010000#0P6PEP0PBP0PBP5P9PG14H4PCP>PIf<REE7R6P3n10110200021010000#0P0PBP5P8PGPLA5C4IR5f=R0C=R<P3n10110200021010000#0%9E91H>R>'6]0P9%06PEPLP5P9O3%0<A1H50'6P1PGPEA5CLIRLf>R1C2A1HL1PGP0A5CEIf?RLC2%9L91HE'6P9PGP1A5C0If@R0C2A5C1IfA51HPGP0A5CLIfBRIC2%9I91HLP8PHPLPIP4P9D_CEW:W;P8P9O2n2001000000120000000bCW0X8BP9O1P:PM16P>/G9b5X0Pn10110100021110000P8O1b9W0W1n0110000020001P9P7O2b1b8b0PGP7P8%9@R@C2A1H8@'6eW0X2DX3FX>JX4;P9C^X4;o"). Qed.

(* [comment removed for export] *)
Lemma write_to_mem_restrict : forall bs m a,
  range_avoids H a (length bs) ->
  write_to_mem (mrestrict H m) a bs = mrestrict H (write_to_mem m a bs).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01ah12Exh21mh31nh42bsh52H0h63Havh71bi001bh82b1h92b2h:1xh;2Hah<3Htlh=2IHh>2b0h?1op;1p;2p;3p;4p;6p;5p;8g002kj16Tg003Pj1FTg003nj12Tg00FOj1ITg00h5j1STg01X4j2:Tg00Xfj3;Tg010?j25j3=Tg01XTR0j31j2Cj1BTg004Qj30Tg00Eoj1HTg00Bnj23Tg00cRj3@Tg01YXj4RTg01ZXj4QTg00?=j1PTg00ABj2NTg00?[j3ETg00@>j3>Tg01[Xj38Tg01Lgj29Tg00ZWj1KTg01\Ej2ATg01\bj2JTg004kj27Tg005Uj3LTg00:Bj6DTg016=j5MTg00OTj8?Tg00\Tj6GTg01]Bj5OTg00WfR1f0R2g00XF30p=<g00=bR3f1R4;02p=4g00<DR5#6#6#6R6#F#2R7#IR8P7%66#6#6#FR6#2R9%S7R:[R;p,1HR<f2R=,:77;215<=R>f3R?714A1=4?,5<50;[^09]2R@X48%H7RA,:79;<2A1=4A,5<,3;W6X09X2;f4RA=@7?,:79;<2P<P41:7AP2CRP<P4O1g00]RRB501P<P=f5RC,:7RDP4CQ%P5R5g00STRE1N65d5E69>6==;<DP;P1P:A862ARDf8RF,97RGPCP2O1n0100000020000X09RH,5<RIAE65ERE9>6?R5f6RJ31P1P:A862CRKf9RL,97RMA=<J2n0100000020000X09A>6AEf7RE31=0;2X?;P8P;P1P:PDPGA=<C2n0100000020000RGX09RN/C51CI5PJPJP9P;\8RO%BN%BIP5P5P;PO\9ROP0P0PNPIPO\;/30P9P:PNPIPDP11312A864C=012P1A86?E=012P1P:P4f<,97RDP1P:P<PAO1RI%K7RNPLPAO1R0n0100000020000n0100000020000P1P:PIPNP1P:P4PDP0n0100000020000n010000002000050:]1P4A86=JR0#<g00=GRD1A42#<14=4[RI14421A=4#<RO[14?=\O1J42P4n2001000000120000000X23X33PI^23^33P2176AR3176FRIP4O3143Ig00<iRI%22R3%24ROPD%2=?04217?=17?4'4RD[17=417=2'4%2??0=4[RP%2A?0?=\DAL=42P2n2001000000120000000W9W8W3PP^9O^83^3IP2P6PJf:R6P4O4A09J6P9f;R6f@,97RIP1P:P<P2O1PNPIn010000002000050:X:9P1PBP1P:P2PNPIn010000002000090:IX71f?,97,3:P<P6O1PLEDPEP2EDb1b5b1b5W1A010BP1P:P<P?O1PNPFP?O1n0100000020000,3:W1n0110000020100P2O1b1b>P1P:PKPMPJP2O1n0100000020000X09==<290:GeX:9DMG?1395G?138JG?A1H5J,5<PCPHP5P2O3EGb<b;A@7CARC91>4A1=4C,5<50;eW6X09X2;X=@X48X77P2DOW4o"). Qed.

Lemma write_to_mem_hidden : forall bs m a x,
  range_avoids H a (length bs) -> H x = true ->
  write_to_mem m a bs x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02Exh12Hxh21mh31ah41nh51xh62H0h72bsh83Havh91bi001bh:2b1h;2b2h<2Hah=3Htlh>2IHh?2b0h@1ehA1op;1p;2p;3p;4p;6p;7p;5g002kj13Tg003Pj1ATg003nj11Tg00FOj1CTg00h5j1NTg01X4j28Tg00Xfj39Tg01XTj4;Tg004Qj30Tg00Eoj1BTg00Bnj2:Tg00cRj3<Tg01YXj4MTg01ZXj4LTg00?=j1KTg00ABj2GTg00?[j3>Tg00@>j3?Tg01[Xj37Tg01Lgj26Tg01\Ej2=Tg01\bj2FTg004kj25Tg005Uj3ETg00\Tj6@Tg01PQj2HTg00:Bj7Dj6ITg01]Bj5JTg00WfR0f0R1g00XFR230p=2g00=bR3f1R4;01p=4g00<DR5#3#3#3R6#A#1R7#CR8P7%36#3#3#AR6#1R9%N7R:[R;p,1HR<f3R=,87794P<P4O1#2R>f4R?P=f5R@f2RAC;P?PAO1RB50:[[^59^39]2RCX78%B7,8799<41::BX1>W8X59X39X2;A<7@?,8799<4P<P=f6RD,87P4CMP<P=O1g00]RRE500P<P?f7RF,87RGPACL%K5R5g00STRH1G65d5>69?6?=9<GP:P0P:A76?@RGf9RI,67PDP?O1RJn0100000020000RKPFP@O190:1XA:PGP01:01A76@D=001P0f8RG976F=001P0P:P4f=RL,67f:RMPGO1RNn0100000020000=0:N]0P4A76DFRN#2g00=GRO1=41#214A4[RP14411=A4#2RQ[14=A\Q1F41P4n2001000000120000000X23X43PP^23^43P1156GR3156IRPP4O3143Pg00<iRP%11R3%14RQPO%1A?04115=A15=4'4RO[15A415A1'4%1=?0A4[RR%1??0=A\OAEA41P1n2001000000120000000W;W:W4PR^;Q^:3^4PP1P6PMf;RPP4O4A09MPP9f<R3P<P1O1#2fB,67f?RQP4O150:]1X59P<P3O1#2P0P<PLO1%21X90P1PEPIE@A00E2P0PEP0p-0P1g00c5RLg01RSn0110000020000X@0PHP2P1E@PLfC,67f@PQO150:/H1b6b1W1PPP1PIFDb0b6b0b6W0A00NEPIPFO1,::W0n0110000020100P1O1b0b?A0:KJeP0P:A761D167MPFP1O1n0100000020000X39RMA>65H9?6@R@PGP?C;PFPMP@P?P1PAO5EIb=b<P?P=A<7FDPAC;=0:BeX1>W8X59X39X2;X>CX78X97P1DJW7o"). Qed.

(* [comment removed for export] *)
Lemma mrestrict_visible : forall (H0 : word -> bool) m a,
  H0 a = false -> mrestrict H0 m a = m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "h02H0h12Hah21ah31bh41mp;1p;3p;2p;6g002kj10Tg003Pj13Tg003nj12Tg00h5j14Tg004Qj31Tg00ZWj18Tg00Bnj27Tg00:Bj65Tg010?j36Tg00<D#0#0#0R0#0#0#0#3#2R1g00WfR2[%30#2R0#4R3\1f2R4f0R5O1g00]RR6512P2P6P2P3P5%80f3R0P4O1R6n0100000020000=136X32P4f1R2O1R6,73P0P2O1P5E5A6042=136eW1X21W4W0o"). Qed.

Lemma ov_read_bytes_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  ov_read_bytes segs (mrestrict H0 m) a n = ov_read_bytes segs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01ah11mh21nh33Havh42H0h52IHh61bi001bh71oi011li022l0i034resti041xp;1p;3p;2p;4p;6g002kj11Tg003Pj16Tg003nj1<Tg00h5R0j1:Tg00Xfj37Tg00FOR1j1DTg010?j23j3ATg01MIj40Tg004Qj32Tg00Bnj2;Tg00@cj19Tg00ZWj18Tg01Lgj25Tg01Jej3>Tg00?=j1FTg00?[j3ETg00@>j34Tg00cRj3CTg01ZXj4BTg00:Bj6=Tg01YXj4@Tg01R2j4?Tg00<DR2#1#1#1R3#1#1#1#6R4#<R5g00WfR6[g00RQR7%63#<R3#:R8\5R9f4R:f0R;f2R<37%D3R=#:R>p,4segsR?f5R@/3<f1RAf3RBC0P?P<PAPBC032[^05]1RCX27g00>@RD97B;P?P<PAPDC0,;>W3X05X19%9B97@;P6g00]RP0P3P>P0P3P8P6P8P;%83RDPBP<O1REn0100000020000153;RFP0P=P8%62RG9>?<P1P3P8P;PD153An10110100020020100102R1PDn10110400021010100RHn10110400021010000P0P=P>P?f8/3:%F2g00ST5E4R2944BRIf6RJC0AC3A;,5=RK%8=RLn10110400021010300PLn10110400021010000P0P3P>P0P3P8PEPFPHn10110400021010000RHP0P=P>P?P:PIPJC0PKPLn10110400021010300PLn10110400021010000RI52>X66P>P?P<A44A2R6P:C0P0P3P>PHP0P=P>PAPKPLn10110400021010300PLn10110400021010000=2>IX7>P0P3P>P0P3P8P<PAO1PFP0P=P8A>?AGP1PDn10110400021010100RDn10110400021010000P0P=P>P?PBA44<2R2P@C0PKPLn10110400021010300PLn10110400021010000R4,;>P?13J<R1P6P:C0PBP<P6PJPAP:P;CBO3E=PJPAO1PJPAP:P;C@E=P0P3P>P0P3P8AAJ<APFPDn10110400021010000P0P=P>P?f7/3BP2P@C0PKPLn10110400021010300PLn10110400021010000=2>4eP?P1PA%9:R:C0P?P<PAP:C052>eW3X05X19X5CX27P;C?W2W4o"). Qed.

Lemma rdn_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  rdn segs (mrestrict H0 m) a n = rdn segs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "h01oh12H0h23Havh31ah41mh51np;1p;3p;2p;4p;5p;6g002kj10Tg003Pj19Tg003nj14Tg00h5j13Tg00Xfj3<Tg00FOj1;Tg010?j25Tg01MIj41Tg01]dj42Tg004Qj36Tg01^Xj5:Tg01_cj47Tg00\Tj68Tg00<D#0#0#0R0#0#0#0#9#4R1g00Wf[g00RQ%90#4R0#3\1f3R2f0R3f2R43<%;0#3R0p,4segsR5f4R6/54R7f1R8P2C1P5P2P4P6C29603X00P0P5P4P8P2C1P5f5/52P4P6C1=603X00P6P2P4P8P3D:P5P4P8P2C2P5P4P2P8C7E8P5P7P8P2C2P5P7P2P8C7E8W2X31W4W5W1o"). Qed.

Lemma wview_mrestrict_eq : forall (H0 : word -> bool) m a,
  H0 a = false -> wview segs (mrestrict H0 m) a = wview segs m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02H0h12Hah21ah31bi001bh41mi013segi021xp;1p;3p;2p;6g002kj10Tg003Pj19Tg003nj14Tg00h5R0j1=Tg004Qj32Tg00ZWj1CTg01Lgj2?Tg004kj21Tg00?=j1>Tg01Iaj36Tg01Roj1<Tg01Daj1;Tg01E`j1:Tg01F^j1DTg01G<j28Tg01GYj15Tg01T1j27Tg00Bnj2BTg00:Bj6ATg010?j2@Tg01U8j33Tg00<DR1#0#0#0R2#0#0#0#9R3#4R4g00WfR5[%92#4R2#=R6\4f2R7f0R8O1g00]RR9525P5P9P0P2P6P5P6P8%C2R9f3R:P7O1R;n01000000200001?28R<P0g01KhR=P6p,4segsR>1137R?%>1R136P5P6%<8R@%;8RA113:%:8#DRB'8#5'7P9n0100000020000P9n10110200021010100RCn10110200021010000P0P2P6P;P<PCn10110200021010000526X35P0P2P6P7f1R2O1P<P0P=P61132=6>1P5P6P@18?B#5,7AP9n0100000020000P9n10110200021010100n10110200021010000,B6P:P2O1P8EA1@:7=3>2A3>72526eW1X24W4W0o"). Qed.

Lemma store_ok_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  store_ok segs (mrestrict H0 m) a n = store_ok segs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01ah11mh21nh33Havh41oi001oh52H0h62IHh71bi011bi021xp;1p;3p;2p;4p;6g002kj11Tg003Pj19Tg003nj18Tg00h5R0j1=Tg00Xfj35Tg010?j23Tg01W4j40Tg004Qj32Tg00Bnj27Tg00@cj16Tg01U8j34Tg00?=j1<Tg00?[j3;Tg00@>j3:Tg01ZXj4BTg01YXj4ATg01`Zj4@Tg00:Bj6?Tg01R2j4>Tg00<DR1#1#1#1R2#1#1#1#9R3#8R4g00WfR5[g00RQR6%92#8R2#=R7\4R8f4R9f0R:f2R;35p,4segsR<f5R=/3;f1R>f3R?C0P<P;P>P?C0525[^04]1R@X26g00>@RA95?:P<P;P>PAC0,75W3X04X18%6?95=:P7A4<;>RAP0P2P5P:P<f8/39%<1g00ST5;3R19:3?RBf6RCC0g00]RRDn10110200021010100P0P2P5A4<?;P<P9PBPCC0PDn10110200021010100525X47PAP7P0P2P0P2P5P:P<f9R7/3=A:391R1f7R3C0PDn10110200021010100P0P2P5P:P<P=P1P3C0PDn10110200021010100525P:PCP=P1P7P9P3P?CBO3X72P:O1175Dn10110000021010100b413C;RD=4<>PCP;P>PCP>P9P:CAC@E?P<PDP>%69R9C0P<P;P>P9C0525eW3X04X18X6@X26P:C>W2W5o"). Qed.

(* [comment removed for export] *)

Lemma find_segment_some_spec : forall l addr n seg,
  find_segment l addr n = Some seg ->
  In seg l /\ (Z.of_N (seg_base seg) <= addr)%Z
  /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01Eh12H0h22Hfh31nh44addrh51lh63segh72E1h82E2h92b1h:2b2h;1eh<1mh=1si001sh>2H1h?2H2h@3HinhA2IHhB1ahC1bi011bi021op;1p;3p;2p;6p;4p;7p;5g00FOj1QTg00h5R0j1PTg01Iaj3;Tg004Qj37Tg00ESj20Tg006Yj24Tg00=GR1j26Tg00Eoj1CTg00\Tj6BTg01PQj2OTg01a]j21Tg01b:j29Tg00Bnj2ATg00d2j6NTg01bXj2MTg01c9j2LTg01cYj3JTg01O2j4>Tg00:Bj7ITg01d3j3HTg01]Bj5GTg01Lgj2FTg01E`j1KTg01F^j1?Tg01dMj1ETg00aaj3@Tg00cRj3DTg01KhR2f0R3'Fp==%K3#?p=3f1R4%E3#?'4p=5f2R5=@24/63p=8AD243p=:g00WfR6g00XF773p=2A@243p=<%Q2R7P2g00=bR8%P2R9f3R:?;54%=3R;37f4R<%34R=/0:14:5R>15=4'0'6584[^62^38]4R=X57%C2R??;54=79;P9A;?:5P0P2p-0P3g00c5R@g01RSn10110200021000000X;9g00ST%=4P3EBP@%35R@/0<14<:RA15@5'0'6985?/O3b1W2X62X38X48f5R?/:<?;54=79;f6R;#3R@/1:15@;RB,1>'9P61A63f7R>#3RC/1<15C>RD,1A'9=763P6f9RA#3RE/1;14;?15EARF'1'9=763P6P9P4f:RG#=RHA;A>;n0100000020000%=?RI579f;RJ/:Gf8RK,0@14K>/0B'6RB58;]2]0P4%3KR@/1?14?<15@K'1'9R@#2%=A%=<R<579P9P2P0P2P2P3P3PJn10110200021010000X;9PHPIP3ENA72G?A72J;P2P>%33RI/1G14GA15I3'1'9#2f=RI,:410EJ14JGRH/0F'6R058A]0X=211CA14AKRL/1D'9#2P11943#2%25RM%24RN'6[RO%23,6N1954#2RN[%2:/6M\N1M43P4n2001000000120000000X:6X96PO^:6^96P311EJRE11HFRHP4O3%2E%2H'6P1%3GRHf<RE'1#214EJRF15HGRO'1#2f?RN,:J%3JRM/0I14IE15MJ'0'6RM58JP3%3ERPf>RQ'1#214NQRR%3I/5IRI'1#2P11143#21054[RS10431154#2RT[10:5\T1L43P4n2001000000120000000X<8X38RTPS^<8^38RSP3%3NRUfARVP5O310UVPTPSP3fCRSfBRT'4RU%3V/5VRVP:O310UVfFRV,:T,<T%3TRUfDRW'0RX14WS15UT'0RU'6A72TT1<TV1A2T3JPXPUP5P3C>C>b8b1b7b1W8W7P4P3O2n2001000000121000000b0b1W0PEP3P:FIW1P3O1b1W2W0g00]R976@A;K;?=79<PKP>P;P?P3O4%3?R</0>14>;15<?'0'698?AP11<;GPB1:EJ10CA10LD'658>P31<KEP110HE10FOf@RO/:N=8JMP310PQ10RI1:ST,<Q%3QRI/0ORR14ON15IQ'0RI'6A72SQ1<QT;H?PRPIP4P3C>C>W?W>P4P3O2n2001000000120000000X10W@P4P3O2n2001000000120000000bBW2W0n0110100020101P3P5O2b0bCW2X62X38X48XA=X57X=2P3DGW5o"). Qed.

Lemma find_segment_none_spec : forall l addr n,
  find_segment l addr n = None ->
  forall seg, In seg l ->
    ~ ((Z.of_N (seg_base seg) <= addr)%Z
       /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01Eh12H0h22Hfh34__p1h44__x1h54__x2h63segh73Hinh84addrh91lh:1nh;2H1h<7__arithh=4__ffh>8__varmaph?5__with@4__x3hA4__x4hB2b1hC2b2hD4cstrhE5cstr0hF1xhG1yhH2H2hI2IHhJ1bi001bhK1ehL1si011op;1p;3p;2p;6p;4p;5p;7p;8g00FOj1RTg00h5R0j1dTg01Iaj3=Tg00ZWj1JTg004Qj34Tg00aaj3>Tg00ESj25Tg006Yj20Tg00=GR1j2:Tg01eKj1;Tg00Eoj1HTg00cRj3QTg01a]j22Tg01b:j29Tg00Bnj2PTg01Lgj2GTg00\Tj6NTg01PQj2XTg00dOR2j2@Tg01edj2WTg00Z;j2<Tg01fFj2VTg01E`j1MTg01ffj1LTg01F^j18Tg01dMj1?Tg00Foj2FTg00GMj1UTg00Gkj4ETg00HIj1TTg00Hgj1STg002kj1ITg00IRj2ATg00K;j4BTg00LJj2cTg00Llj2bTg00MXj3aTg00N7j4`Tg00kaj1_Tg00JXj3OTg01]Bj5[Tg00Kfj7ZTg01NNj6^Tg00[9j8YTf0R3#M#8p=1f2R4f1R5%?3#8'0'5p=6%?3#8,05p=7g00WfR6g00]R743p=3P5g00U@R7g00U_R8P8g00V?R9P3g00WFFZp=CP5P7P8P8P9P3E^p=Kf3R:P7P8P8P9P4P5P3GYp=D1053,54p=]%?3#8p=\g01KhR7#RR;P7g00=bR<%d7R=A=453%J7R>34f4R?9>73%15R@/5?10?:RA?6@5':#;[^67[^:<]8R@X9;%H7RB?=53=4=>A>73Bg00c5RB%14RCf5RD'510D?RE?6C4':#;P3n010000000W7X67W2X:<X8<AQ7?:?=53=4=>f6RC=Q7D9>73f7RF#1RG/2?17GF,2A'9P61P63f8RA#1RG/2D17GA,2E'9=463P6f:RE#1RG/2F10FC17GE'2'9=463P6P=P5f;RG,G7A=EAFn0100000020000=4=>%1CRHf9RI'510IA?6HC':#;RH]2]0P5%1IRJ/2C10CD17JI'2'9RJg00XFRK5461G7E=4=>%1DRL/5A10AF?6LD':RLP=f<RA,G7P0P7p-0R0P3g01RSPBn10110100021000000XK=g00STP>P5ENPB1XB3b;W1%;LeW2W0%3JA=IFC=4=>P2A47GDA>7DEPHP?A47ACP7f=RA%13RH/5G10GERD?6H3':#;X67%1ARH/5E10EI?6HA':RHP1f>R>#1R=/5GA6D=>PBP3f@R=#1/5A10>AfAR>#1;6>P11953#3%34RA%35RD'@[RJ%33,@D1945#3RD[%3:/@A\D1W53P5n2001000000120000000XC6XB6PJ^C6^B6P3fCRJ#1RD/2=RAf?,0=17DJ'2RDPIO3%3A%3D'@P2fDR2#1RD/2>#310>=17D2'2#3PBP3fERD#1R=fBRA'2#3P11253#31<54R1[RL1<351245#3RM[1<4:\M1V53P5n2001000000120000000XG<XF<RMPL^G<^F<RLP3fGRN#1ROP2P5O31<2OfHRP#MRQ#LRRg00>_RS%8Q'5RQfI#?RT#LRU%8T,5SRTg00TTRV#HRW%RVRVP<1F<4P5%U<RXCE%T<RY%S<RZP<g00<DR[#IR\,A<R]g00^2R^1A<[R_CB,CZ%J8R8PZP<P_g00^YR`P]CB,CZP81KZ?CDCD1cZ9R9P3P41P6K1b34=46KdAa<S5C`RSb=b>b?X4<X5<X301553P?\1[^4<^5<^30P3PBfKR1#1RKPPPEP:O5b<bEbDb0b1W0P3O110A>17=D'2#3PMPLP3102JR217ONROP5O31<O2PRPQPUPTPWPVP<P<1F<?P4PXCEP51F<:CEPYPZP<%_[,A<%I\,A<5O<R\P^AO<_]R_CB,CZP8PZP<P_P`P\CB,CZP81KZCCDCDP9PSb=b>b?X4<X5<X@<XA<X30104:?]35105410:?'<PC[[^4<^5<^@<^A<^30P3PBPNPP%\1PKPIP:O7b<bEbDb0b1W0P3O1n200100000021000011000b0b1WHW;P5P3O2n2001000000121000000W1%;HePFP3ENW1P3O1A>7CGPGPEPIP4PFP3O5W7P3O1n200100000021100010000W2W0n0110000020001P3P?O2b0bJW7X67W2X:<X8<XI@X9;XL7P3D[W9o"). Qed.

(* [comment removed for export] *)
Lemma in_segment_not_hidden : forall (x : word) seg,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned x)%Z ->
  (bv_unsigned x + 1 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  H x = false.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h02Hxh12H1h22H2h33Hinh41bi001bh53segh61xp;1p;3p;2p;4p;7g002kj10Tg003Pj1?Tg003nj1;Tg00aaj39Tg01E`j16Tg01F^j12Tg004kj25Tg00ESj23Tg00?=j1:Tg006Yj24Tg01dMj17Tg00Bnj28Tg004Qj31Tg01O2j4>Tg01gIj7=Tg01PQj2<Tg00<DR0#0#0#0#0#0#0#?R1#;g01KhR2f0R3p,4segsR4592f1R2#6#2f2R5,51'3f3R6,51%:0R0'4%65#2%75#2'4'3p,1HR5f4R7O1g00WfR81883P5f5R9O1=183P8P5f7R:O1=183g00]RR;9182]0P2P5f6R5O1R2g00XFR<518A18<;P4151:R1P0p,2HHP:P3O2P5P9%65#2R9/311410%75#2,49'3P7P6C>F='<W0A182;188;W0n0110000020000P3O1b0b4W2W1W3W5W6o"). Qed.

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z ->
  seg_ov_read_bytes (mrestrict H m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h04__x1h14__x2h21mh34__x3h44Hhi0h57__arithh64__ffh76__sat2h86__sat3h98__varmaph:5__with;4__x4h<4cstrh=5cstr0h>5cstr1h?3Hhih@1ahA3seghB2IHhC1ni001nhD1xi011xhE2HahF2H0hG3HinhH3HlohI4HtophJ4__x5hK1zhL2H1hM2H2hN3Hu1hO1bi021bhP2n'hQ1ohR1yi034restp%0p&0p;1p;3p;2p;4p;5p;7p;6p;<p;Bp;8g002kj1CTg003Pj1lTg003nj1cTg00h5R0j1bTg00aak30>Tg004kj21Tg00ESR1j27Tg0069R2j13Tg006YR3j20Tg00?=j1ZTg01hPk20=Tg00FOj1kTg010?j2Oj3sTg01hmj42Tg004Qj3:Tg00Bnj2NTg00@cR4j19Tg00CHk102Tg00Cfk400Tg00_@j4^Tg00Dnj1aTg01E`j1STg01ffj1ETg01F^j1ATg01dMj1RTg01j6j2oTg00Z;j2BTg01j^j3nTg00Eoj1mTg00Foj2QTg00GMk10<Tg00HIk10;Tg00Hgk10:Tg00IRj2ITg00ZWj1_Tg00LJk209Tg00Llk206Tg00MXk305Tg00N7k404Tg01kBj2KTg01kkj3LTg01lTj2]Tg00cRj3WTg00J5j2\Tg00kaj1gTg01m@k503Tg01Lgj2fTg01Daj1DTg01G<j2GTg01GYj1FTg01T1j2HTg00?[j3eTg00@>j3=Tg007\j2dTg00ABj2|Tg008Bj2{Tg00Aej1zTg00=GS00j2[Tg01nFj3yTg00K;j4MTg01nij7wTg0095j3vTg00:Bj6YTg00PXj3uTg01oMj1}Tg01okj2~Tg020Lj3tTg00Nik401Tg01R2j4rTg00QFl<hTg00QklBqTg00DIm<07Tg00Gkk408Tg00Kfj7XTg00[9j8`Tg00JXj3pTf0R5#S#Ap=<%R5#Ap=;f2R6f1R7'0/75p=5g00=bR8/N5p=8g00RQR9P9P8P8P4P2P2f3R4g00S0P6P7P5M<hp=JP9P8P8P8P2P2f5R2f4R:P4P6P7P5M<hp=VP8P8P8P8P8P8P3P5P7P6P3P4P:P2f6R3f7R;f8R<f9R=MBqp=UA:875p=>P8P8P1P;P1P3P2P:P4P6P7P5N<07p=Tg00>_R1/75p=4P8P6P7P5H08p=?P6g00U@R>g00U_R?P?g00V?R@P8P7g00^2RAP5CMg00WFRBFXp=PP4P>P?P?P@P6P7P5G`p=jAp875p=6P2P>P?P?P@P:P>P?P?P@P8P4PAP6CMPBFXP7P5G`p=@P7P>P?P?P@P5PBFXp=xP:P>P?P?P@P4P>P?P?P@P6PBFXP7P5G`p=ig00<DRB#CRA#CRC#CRD#C#C#CRE#lRF#cRG%lD#cRD#bRH[RIg01KhRJp,4segs:0>J7RK%<611F7'7RL11F6RM%32S01%<4%;4'0RN35%<:%;:%ZARO%ZERE+0=RP35RQ%kDRR#bRSp,1HRT/O3S02P2P:P;C2P3P2P:P;C23:[[[[^@G]A]2RUXC9g00>@RV#3=5MNS03P3P2P:PVC2S04,NSXIQW?XHLXGKX@GXAJX2I%93#3=5MNP:P2P411F:RW%9<S05#3RX'0RY%<2RZ%;2R['0R\'7%3<R]%ZBR^'0=5W\R_P5XD8R`1775$02XR8XD8S06PYP`105^XD8RYP]O1RaO1Rb,0WP`P`P`P8P8g00T01075H00#8X28XC8S07PWPW%8WPXPbP`P`%35#8XD9RbQ05PaPYP<P]%8]CJEVM:UP\P`PZO1P`P[O1'0R[%8[1>\[eGTP7C^R[P_%a=R\%3=#4RZ%S;R]#ERa%A]R]#4RX%R<RW#ERc%AWRW#4Rd1oOERe1B1O%4E1B1P[[Rf%4ORgg01RSRhAnOE7UWERE%4P\h^EgRgf<Rhf:RiO1S08PHg00TTRj#mRk%kjRl1Q86S09&0<8Rm7?7S0:&0;8Rn&0:8Ro1I8BRp1I8ARq5PoS0;%_?RrQ0;Cj209o@RsP5P6g00WfRtg00XFRu'N20656=:tudB05817H04Rub6b9b:X08X1817571776[^08^18P511FhRvf=Rw#SS0<#ARxPiO3b5b2b7b8b>b=b<b4P[P_P\PZPaPXPcPdPePfPEPgQ08PH%9VRd#9S0=,K8S0>1K8d1K8V5L8Rc5L8g0215RX']=WjkS0?Pl1Q8:S0@??6mS0A1Q84Ra7?7PnPoPo1\81R11I8CRCPrPoPo1\8^RZ,6C,6p%gBS0B,I8R\,6qR_Pr16pZR[=Po_E@E@PsPub6b9b:X08X18X38X;8%44S0C10:^Ry1064Rz557106^S0D104:'7[[^08^18^38^;8P5f@S0E#3S0F%;wPxPvP3P;O6b5b2b7b8b>b=b<b4I03PTP:O1g00]RRv5:tPtPvP0PDPSP0PDPHPtPHP5%_DP<P3O1S0Gn01000000200001fD5Rv%D;11F3S0H/G]#F'HS0In10110100021010200P0PRPS1OT=P<g00STS0J9eF^R{9=F;S0Kf;R|C2AWD75,fRR}%_RR~n10110100021010300P~n10110100021010200P0PDPSP0PDPHQ0GPvQ0In10110100021010200P0PRPSP=P<Q0KP|C2P}P~n10110100021010300P~n101101000210102005:SXOtP911F;S0K%97S0I#3%<<Rt/0W35P0PDPSP0PDPHPiP<O1Pv%D=11F<S0G%<=S0L'G#F'Hn10110100021010200S0MP0PRPS1OT|PiA=F={RWP4C2P}P~n10110100021010300P~n10110100021010200P0PDPSQ0MP0PRPSP|PiPWP4C2P}P~n10110100021010300P~n101101000210102005:S]?^BUP=Q03Q02P2P:PVC2Q045:S\Q[\L\K^@G^AJ^2IQ0H%3d%;;,0]35P0PDPSP0PDPHP=P;O1Pv%D<Q0K/Gt#F'Hn10110100021010200P0PRPSPiP=A=F<{PVC2P}P~n10110100021010300P~n10110100021010200,NSW?WB%92S0K#3=5MNQ02P2P:%9;RNC2P3P2P:PNC25:S\Q[\L\K^@G^AJ^2IQ0GQ0I#9#3Q0L%;='035P811F=S0G11F{S0L'0,dF11FiRN/0^S0I,>5XK8%8^Q0J1|F^d9eF^S0JPGe,1F/>^P8P^11F|RM/05,dF10M^'>XK8Q0I1{Fi%4N%zFRV,BN'[%9:S0H#9S03#3S04,0MS0M%ShS0N#ARt%;hS0O'0R]'7%3:Rd/0^/0^=5M]S0PP`Q06Q0MP`PYPYPdO1S0MO1S0QO1S0R,0MP`P`P`Q07PMPM%8MQ04Q0RP`P`PbQ03Q0QPYQ0HQ0MPYP:Pd%8dCJCJEVM:UP]P`PtO1P`Q0OO1'0Rd%8d1>]deGTP6C^Q0PQ0<#E%4x%a3%33#4f?#RRx#E%Ax#4PePfPEPgQ00fA,1FRx#41BxVfBRx,1FS00/0^Rd#41BdP'[P3fCRd,1F#4fD,1F/BVfGRVfEO1PHQ0=#9R]#9,K81K8]=L8c5L8/]X=WjkPlQ0@9?m6??7aPnPoPoP1Q0B#C,I8R]PrPoPo16]Z/6Z,6pP_PrPoPoP1PpPrPoPoP_1\8O=y8FROPrPoP>P?P?P@APo1[P8P[g00^YPOCM,xoFwE@E@E@E@PsPub6b9b:X08X18X38X;8Q0C10y^=57z%4610:2R[/7P%4y1ByP'[[[[[^08^18^38^;8P5Q0FfHRy#;%<y11FVP=P|P4PdO8b5b2WMWFP7P5O2n2001000000121000000b7b8b>b=b<b4bF5vFQ0LP5EYbL11FWAuF={EYQ0J9=F=,1FQ0G/0^'>PSPhP|A=Fi{RW%94RVC2P0PDPSP0PDPHPwP|O1Pv%Dh1GMt#F'Hn10110100021010200RMP0PRPSP7P}P~n10110100021010300P~n10110100021010200P0PDPSPMP0PRPSf>RMPwA=Fh{Q0KC2P}P~n10110100021010300P~n101101000210102005:SXQSP0PDPSP0PDPHQ08Pv%D|%<|Ry,GN#F'Hn10110100021010200P0PRPSPwPhA=F|{Q0HC2P}P~n10110100021010300P~n10110100021010200,NS1OThP|PWPVC2P6PhP|PWP=%9VR=#3Rh,0NRw%;|S0H,0yR1'7%34R@/0^R?/0^=5N1R>P`Q06PwP`PYPYP@O1RwO1R_O1R],0NP`P`P`Q07PNPN%8NPhP]P`P`PbP=P_PYPVPwPYP4P@%8@CJR@CJEVM:UP1P`PyO1P`Q0HO1'0Ry%8y1>1yeGTP7C^RyP>Q0N#ERY%4tRt%a2RwQ01#4R_%RMR=#ER]%A=#4R=PePfPEPgPxQ0EO1RhPH%}B,~8Q0>5t8=L8c/]X=WjkPlQ09??7aPnPoPoP8Pqg00V_Ra16\ZCMPrPoPoPpP\PrQ0;E@DiPsPub6b9b:X08X18X38Q0D,>717741764[[^08^18^38P5Q00A=Fx{,1FRx%<dRjP<Q0EO5b5b2b7b8b>b=b<b411FWRW%3VRX'0Rc/7110W?RB/71P`Q06PcPBP`P`P`Q07PWPW%8WPXP?P`P`PbPVP?P@EVM:UP1P1%81GTPyP>PYPtPwP_P]P=PePfPEPgPhPHQ0?PlQ0A1Q82??4m7?7PnPoPo%gA,I8RA16qZRm/6Z'616\CR\PrPoPoP8PpPa16AZCMPr16pm=Po\DiE@PsPub6b9b:X08X18X38X;8XJ8107^/0^=5:z102^,>7104^=56[[[^08^18^38^;8^J8P5Q00%;dRdPj%3|PxP;P<O7b5b2b7b8b>b=b<b4H01PyP>PYPtPwP_P]P=PePfPEPgPhPHPkPlQ0:PnPo16pq=PoOROPrPOCjPsPub6b9b:X08X18A557PA576P[^08^18P5PdPjPMO3b5b2b7b8b>b=b<b4O7EYbNW?WBXP9P5O1n0110001020111100P<P6O2PTP2O1P5EYP0PDPSP0PDPHAsT;2Pv%D311F2%<3'G#F'HR6n10110100021010200P0PRPS1OT<P;A=F3{R{PiC2P}P~n10110100021010300P~n10110100021010200P0PDPSP0PDPHP;P2O1PvP6n10110100021010200P0PRPSP<P;P{PiC2P}P~n10110100021010300P~n101101000210102005:SebEQ02P2P:Q05C2P3P2P:Q05C25:SeXIQW?XHLXGKX@GXAJX2IXBUXC9P5CrXC9o"). Qed.

Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h03Ewxh12Hfh22H0h32H1h42H2h53Hinh61ah72a0h81bi001bh91mh:1nh;1oi011oh<3segi023segh=1zi031si041xp;1p;2p;3p;4p;5p;6p;8g002kj18Tg003Pj1FTg003nj1DTg00h5R0j1@Tg004kj22Tg01F^j10Tg01Iaj3<Tg00Bnj2ATg004Qj31Tg00FOj1HTg021aj1;Tg01Roj1:Tg01b:j29Tg010?j2>Tg01H7j1=Tg01hmj45Tg00ZWj1GTg01Lgj2NTg022ej5MTg00aaj3CTg01E`j16Tg00ESj23Tg006Yj2BTg01dMj17Tg00=GR1j2?Tg0069j1LTg023lj1KTg00:Bj6ITg024Ij8JTg025Tj4ETf1R2f0R3#0'Bp=4g00<D#8#8#8R4#8#8#8#FR5#DR6%F4#DR4#@[g00<ip,4segsR71252%033<g01KhR8#@R91A93f2R:,25%025<7=193P0P8f4R;,25f3R<#05<7=193%H4R4#@R=P0P8P=P2g00WfR>P=%;3%:3'9R?p,1HR@f7RA'>P3f6RBf5RC#=RDC5%G4R4n0100000020000P4n10110400021010200P0P8P=P2P>P=P?PAP3PBPDC5P4n0100000020000P4n1011040002101020031]1P2125C%0;5<71N83519%;2%:2'9P>1A>3%;:%::'9=1>3P>%;;%:;'9=1>3P>P=P2f;RD,>@PCf:R?f9R0#=REC5P4n0100000020000P>P=P2PDPCP?PEC5P4n010000002000051=]0P2%;<%:<'9REg00XF51>P71250RFf8RG#0RHP;P<DMAC8;7%6;#0RI/3F1BFH%7;,4I'3'?'?P1AC8C7%6C#0RI125?R;'314;0%7C,4I'3'?f<RI,>@PBPD%=?R;C5PIPBPDP;C551=P3AC8A7%6G#0RAf=R;,25RB'314BI%7G,4A'3'?P1%60#0R1f>RA,25RG'314G;%70,41'3f@R1,>@P?f?RG%=ARBC5P1P?PGPBC551=P3%6D#01251'3fARD,25/41%6I#0%7I'4'3%=DRIfCR1P;fBPCP2g00=bRB%0D1251/B3%6A#0%7A'4'3X=BP3%LI%KDEIp,3HwxP;PCP0O3GJW4W3P2P3O2n2001000000120000000W2W5P2P3O2n2001000000121000000b7W0g00]R91>E1A=4R4W0n0110000020100P3O1b0b8W1X<8P3O1125<%0:5<7%G8519P4W1n10110100021110300P3O1b1b;P71>@:P2P3CEP7P:P2P3CE51=eW:X66W9o"). Qed.

Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01ah11mh21oi001bi012b0i022b1i032b2i042b3i051li062l0i072l1i082l2i092l3i0:2l4i0;1xp;1p;4p;2p;3p;6g002kj10Tg003Pj11Tg003nj12Tg00h5R0j14Tg00FOR1j1CTg025Tj43Tg004kj28Tg00?=j1=Tg00BNj26Tg01\Ej27Tg026Xj15Tg00ZWj1<Tg0276j4;Tg01Lgj2BTg004Qj3:Tg00Bnj2ATg010?j2@Tg027ij3?Tg00:Bj6>Tg028oj39Tg00<D#0R2#0R3#0R4#0#0R5#0#1R6#2R7%14#2R4#4[%C4R8#4R9p,4segsR:f1R;f0R<%13R3C3R=%15#2R5#4R>g00WfR?P>186;%=2R2'6g00>_R@'7#5RA%<5RBP0P8P>P<P1P4P>P<PBP1P4P>P<PBP1P4P>P<PBP1P4P>P<PBP1P4P>P<P;f3f5f7C;,B5PBn1011090002002010010:n10110800020020104109n10110700020020103108n10110600020020102107n10110500020020101106R5PBn10110;00021010500n0100000020001P?P>PAPBP0P8P>P:f2P;P3C3P5PBn10110;00021010500n01000000200013:X29P?P>186</62/7@#5PBP0P8P>P=P5PBn10110;00021010500n0100000020001,A>P:p,1H/@;RBP<P3C3A?;<3E>A9:B<A9:;<5:>eX07W1o"). Qed.

Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01ah11mh21oi001bi012b0i022b1i031li042l0i052l1i062l2i071xp;1p;4p;2p;3p;6g002kj10Tg003Pj11Tg003nj13Tg00h5R0j12Tg00FOR1j1>Tg025Tj44Tg00ZWj1<Tg02:4j2;Tg01Lgj2:Tg004Qj35Tg00Bnj27Tg010?j28Tg027ij39Tg00:Bj6=Tg02:gj36Tg00<D#0R2#0#0R3#0R4#0#0#1#3R5%13#3R3#2[%>3R6#2R7p,4segsR8f1R9f0R:%12R2C4R;%14#3R4#2R<P0P6P<P:P1P3P<P:%<4R=P1P3P<P:P=P1P3P<P:f3,;9,:4P=n10110500020020100106n10110400020020102105n10110300020020101104R4P=n10110700021010300P0P6P<P8f2P9P2C4P4P=n1011070002101030035X27P0P6P<P;P4P=n10110700021010300,7<P8p,1H/89R=P:P2C4A99:2E=A68=:A689:55<eX05W1o"). Qed.

Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01ah11mh21oi001hi011xp;1p;3p;2p;6g002kj10Tg003Pj11Tg003nj12Tg00h5R0j15Tg02:gj33Tg02;lj27Tg01Lgj2<Tg004Qj36Tg00Bnj2;Tg010?j2:Tg02<nj28Tg00:Bj69Tg02>5j34Tg00<D#0#0#0R1#0R2#0#0#1#2R3%11#2#5[%12#2R2#5R1p,4segsR4f1R5f0R633R7P0P2P11745R81<26R9P6n10110100021010000P0P2P1P8P9f2=345n10110100021010000561X21P0P2P11746P9P7n10110100021010000,;1p,1H/:5R7=3461856E9A4476A4456561eX03W1o"). Qed.

Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h01oh11ah21mi002h0i012h1i021xp;1p;3p;2p;4p;5p;6g002kj11Tg003Pj12Tg003nj13Tg00h5R0j14Tg02>5j30Tg004kj27Tg00?=j1>Tg00BNj2=Tg01\Ej25Tg026Xj1;Tg00ZWj1ETg02?;j4DTg00kaj1CTg010?j2BTg00?[j3ATg00@>j38Tg02?fj5@Tg01Lgj2?Tg004Qj36Tg00Bnj2FTg02@Nj2:Tg00:Bj69Tg02AVj3<Tg00<DR1#1R2#1#1R3#1R4#1R5#1#2R6#3R7%23#3#4[%24R4#3R3#4R8p,4segsR9f1R:f0R;30R<%25R5#3R=#4R>g00WfR?P>176:%>2R@'=g00>_RA'5#;RB%E=RCP0P3P>P;P?P>%22R2P4g02B\P2P;CD'7%C1#>'5R1P0P3P>p,1HR2f3RD'Bf2REg00STRF9A6@RG586RH509P5P4P4P;P:D@,?=RIPCn10110200021010100P5P4P4AA4AFP;D@,?=R=n0100000020000PCn10110200021010000n0100000020001P?P>PBPCP0P3P>A09E:RFP?P>P1P0P3P>A09DHPIPCn10110200021010100P=n0100000020000PCn10110200021010000n0100000020001RH36X08P8A86;GRD909:P?P>PBPCP0P3P>PFP?P>P1P0P3P>P:PIPCn10110200021010100P=n0100000020000PCn10110200021010000n0100000020000=6>HX08P?P>176;/=@/5A#;PCP0P3P>P<P?P>P1P0P3P>A86:G909EPIPCn10110200021010100P=n0100000020000PCn10110200021010000n0100000020001,F>1B2:R2=09D1::DE9A092;1::;E9A<92;A<9:;56>eX17W2o"). Qed.

Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (mrestrict H m) a = fetch_failure segs m a.
Proof.
  intros m a. unfold fetch_failure. cbv zeta. rewrite fetch_half_any_restrict. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma interp_eff_accesses_restrict : forall t m c mr' rs,
  interp_eff_accesses segs t (mrestrict H m)
    = MachineOk (@mkAccessReport _ (c, mr') rs) ->
  exists mf',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs)
    /\ mr' = mrestrict H mf'
    /\ (forall x, H x = true -> mf' x = m x)
    /\ ranges_avoid H rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; (* [comment removed for export] *)
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - (* [comment removed for export] *)
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  - (* [comment removed for export] *)
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [| destruct (range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  - (* [comment removed for export] *)
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_accesses_restrict : forall ms w msr' rs',
  decode_exec_accesses segs (restrict H ms) w
    = MachineOk (@mkAccessReport _ msr' rs') ->
  decode_exec_accesses segs ms w
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : forall ms msr' rs',
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ msr' rs') ->
  step_accesses segs ms
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (vdso_text_at segs (ms_pc ms)); [discriminate|].
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

(* [comment removed for export] *)
Theorem step_restrict_sound : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists rep,
    step_accesses segs ms = MachineOk rep
    /\ access_value _ rep = unrestrict H (ms_mem ms) msr'
    /\ ranges_avoid H (accessed_ranges _ rep)
    /\ hclean H msr'
    /\ restrict H (unrestrict H (ms_mem ms) msr') = msr'.
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.

(* [comment removed for export] *)
Corollary step_restrict_step : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  RiscvSemantics.step segs ms = MachineOk (unrestrict H (ms_mem ms) msr').
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) ["ISA"] "p'0h03reph12H0h21mh32Hsh43Hsah52Hvh62_Hh71eh82msh94msr'i001ri016reporti021xp;1p;2p;3p;6g02C:R0j1?Tg017?j24Tg035Jj2;Tg004Qj31Tg038Wj3HTg00fnj1DTg02mcj28Tg02J>j2:Tg02Tcj29Tg00b8j2<Tg01@Ej26Tg02I<R1j2GTg00=GR2j2=Tg02DBj1FTg02Foj1CTg00Bnj2BTg00:Bj6>Tg02S_j2ATg00oAj1@Tg0188j3ETg00i]R3f0R4':p=51A34p=7f2R5f1R6#@;E4p=2A1364p=01=64,=5p=3%?3R7p,4segsR8p,1HR9/46';%54R:31AH564%D3R;%?;R<f3R=,881:;4R>31%74R?A29=5R@'01934,<9RA1695149@/053333X0;'GP1P;f4R1,88=1<>A291=R5,0?169=1495/0=53A33X0;1;81%55517P4f6R5,88=1<>f5R>9295R@,0?169>149@/0>53A33P2f7RA,881:;651<%76A29A5R@'01936,<91695149@/05'=33f8R5,;8A295A#5517P4f9R@,881:;=51<%71f:R==29@RB'01931,<9169@149B/0@'=33P2%7>f;R2=29=RB'0193>,<9169=149B/0=33f<R=,;8A29=2#5517P4%7Af=RA=29='01935,<9169Af>R5=29A,49/0A33P<1:;@P0P;P7P4%5?%F3%C3n1011000003101010000f@f?R?529#5R0517X2<P3A29?5R5A17:0X23%55R5,B7%7@P6E>188?P>E>1;8?=175eW6W5P6P4O2n2001000000120000000W1W4P6P4O2n2001000000121000000W1X0;P6P4O2n2001000000121102000b7W3X93X83o"). Qed.

(* [comment removed for export] *)
Lemma step_accesses_ecall_shape : forall ms msr' rs',
  step_accesses segs ms = MachineOk (@mkAccessReport _ msr' rs') ->
  ms_svc_pending msr' <> None ->
  rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
  /\ ms_svc_pending msr' = Some (ms_reg ms 17).
Proof.
  intros ms msr' rs' Hs Hsvc.
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
            rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
            /\ ms_svc_pending msr' = Some (ms_reg ms 17)).
  { intros w Hd. unfold decode_exec_accesses in Hd.
    destruct (is_ecall w).
    - injection Hd as <- <-. cbn. repeat split; reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
      exfalso. apply Hsvc. reflexivity. }
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (vdso_text_at segs (ms_pc ms)); [discriminate|].
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

End ISA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
  existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
                     && (bv_unsigned p + page_size <=? snd iv)%Z) A.

(* [comment removed for export] *)
Definition A_wf (A : list (Z * Z)) : Prop :=
  Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
                    /\ (snd iv) mod page_size = 0)%Z A.

(* [comment removed for export] *)
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

(* [comment removed for export] *)
Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
    (A : list (Z * Z)) : Prop :=
  forall w : word,
    page_in_ranges (page_base w) lazy = true -> H w = false ->
    page_allowedb A (page_base w) = true.

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 ->
  same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : forall m mat',
  same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m  (* [comment removed for export] *)
  /\ m_fds m' = m_fds m /\ m_pipes m' = m_pipes m /\ m_stdin m' = m_stdin m
  /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m
  /\ m_rlimit_core m' = m_rlimit_core m /\ m_clock m' = m_clock m
  /\ eager_used m' = eager_used m.
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  repeat split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
  match A with
  | [] => []
  | iv :: r =>
      map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
          (seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
      ++ A_pages r
  end.

Lemma Zmod0_multiple : forall a, (a mod page_size = 0)%Z -> exists q, a = (page_size * q)%Z.
Proof.
  intros a Ha. exists (a / page_size)%Z.
  pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
  rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.

Lemma A_pages_length : forall A,
  A_wf A -> (Z.of_nat (length (A_pages A)) * page_size = A_bytes A)%Z.
Proof.
  induction A as [|[lo hi] A IH]; intros Hwf; [reflexivity|].
  cbn [A_pages A_bytes fst snd]. inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst.
  cbn [fst snd] in *.
  rewrite length_app, length_map, length_seq, Nat2Z.inj_add, Z.mul_add_distr_r.
  rewrite (IH Hwf').
  destruct (Zmod0_multiple lo Hlo) as [qlo ->].
  destruct (Zmod0_multiple hi Hhi) as [qhi ->].
  replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  rewrite Z2Nat.id by (unfold page_size in Hle; lia).
  reflexivity.
Qed.

Lemma A_pages_in : forall A p,
  A_wf A ->
  (bv_unsigned p mod page_size = 0)%Z ->
  page_allowedb A p = true ->
  In (bv_unsigned p) (A_pages A).
Proof.
  induction A as [|[lo hi] A IH]; intros p Hwf Hal Hpa; [discriminate|].
  inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst. cbn [fst snd] in *.
  cbn [A_pages fst snd]. apply in_or_app.
  unfold page_allowedb in Hpa. cbn [existsb fst snd] in Hpa.
  apply orb_true_iff in Hpa as [Hpa | Hpa].
  - left. apply andb_true_iff in Hpa as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (Zmod0_multiple lo Hlo) as [qlo Eqlo].
    destruct (Zmod0_multiple hi Hhi) as [qhi Eqhi].
    destruct (Zmod0_multiple (bv_unsigned p) Hal) as [qp Eqp].
    rewrite Eqp in *. rewrite Eqlo, Eqhi in *.
    replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
    rewrite Z.div_mul by (unfold page_size; lia).
    apply in_map_iff. exists (Z.to_nat (qp - qlo)).
    unfold page_size in *.
    split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. lia.
  - right. apply IH; [exact Hwf' | exact Hal | exact Hpa].
Qed.

Lemma NoDup_map_bv_unsigned : forall (l : list word),
  List.NoDup l -> List.NoDup (map bv_unsigned l).
Proof.
  intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
  apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.

Theorem allowed_pages_bound : forall A (pages : list word),
  A_wf A ->
  List.NoDup pages ->
  (forall p, In p pages -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p pages -> page_allowedb A p = true) ->
  (Z.of_nat (length pages) * page_size <= A_bytes A)%Z.
Proof.
  intros A pages Hwf Hnd Hal Hpa.
  rewrite <- (A_pages_length A Hwf).
  assert (Hlen : (length pages <= length (A_pages A))%nat).
  { rewrite <- (length_map bv_unsigned pages).
    apply NoDup_incl_length.
    - apply NoDup_map_bv_unsigned. exact Hnd.
    - intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
      apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_woff : forall a k,
  page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
  intros a k. unfold page_base, woff, page_base_of.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  assert (Hz : (0 <= z)%Z) by (unfold z; lia).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !two64_as_pages.
  set (r := (z mod (page_size * 2 ^ 52))%Z).
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  (* [comment removed for export] *)
  pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
  fold r in Hdm.
  set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
  assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
  { rewrite Hdm at 1.
    replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hfl.
  replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
    with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma page_base_of_aligned : forall z,
  (bv_unsigned (page_base_of z) mod page_size = 0)%Z.
Proof.
  intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
  rewrite (Z.mul_comm (z / page_size) page_size).
  rewrite Zmult_mod_distr_l.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma page_insert_nodup : forall p pages,
  List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages Hnd. unfold page_insert.
  destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
  constructor; [|exact Hnd].
  intros Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma page_mem_false_not_in : forall p pages,
  page_mem p pages = false -> ~ In p pages.
Proof.
  intros p pages Hm Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages Hin. unfold page_insert in Hin.
  destruct (page_mem q pages); [right; exact Hin|].
  destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
  - left; exact Hin.
  - destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin''.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
  - left; exact Hin.
  - destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : forall H A lazy mat ranges,
  lazy_cover H lazy A ->
  ranges_avoid H ranges ->
  let new := newly_materialized_pages lazy mat ranges in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ (forall p, In p new -> (bv_unsigned p mod page_size = 0)%Z)
  /\ (forall p, In p new -> page_in_ranges p lazy = true)
  /\ (forall p, In p new -> page_allowedb A p = true).
Proof.
  intros H A lazy mat ranges Hcov Hav new.
  assert (Hchar : forall p, In p new ->
            page_in_ranges p lazy = true /\ page_mem p mat = false
            /\ exists a n k, In (a, n) ranges /\ (k < n)%nat
                             /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
    destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter.
    apply accesses_pages_nodup. constructor.
  - intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
    apply page_base_of_aligned.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
    pose proof (Hav a n Hin k Hk) as Hw.
    rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
    exact (Hcov (woff a k) Hl Hw).
Qed.

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : forall l X m,
  m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_halted_wvb : forall l X m, m_halted (with_vm_backing l X m) = m_halted m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Xh11lh21mp;1p;2g002kj10Tg003Pj17Tg003nj13Tg00`aj22Tg00FOj11Tg00h5j16Tg03RRj15Tg00Bnj24Tg00<D#0#0#0#0#0#0#7#3R0/20#1%10g03<3%60f0#5'4W2W0W1o"). Qed.
Lemma eager_used_wvb : forall X m,
  eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma MInv_wvb : forall A m X,
  List.NoDup X ->
  (forall p, In p X -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p X -> page_allowedb A p = true) ->
  (forall p, In p X -> page_in_ranges p (m_vm_lazy m) = true) ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A (with_vm_backing (m_vm_lazy m) X m).
Proof.
  intros A m X H1 H2 H3 H4 H5. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
    assumption.
Qed.

(* [comment removed for export] *)
Theorem materialize_restricted : forall H A m ranges,
  lazy_cover H (m_vm_lazy m) A ->
  A_wf A ->
  MInv A m ->
  ranges_avoid H ranges ->
  exists mat',
    materialize_model_accesses m ranges
      = Some (with_vm_backing (m_vm_lazy m) mat' m)
    /\ MInv A (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
  destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
    as (Nnd & Nfresh & Nal & Nlz & Npa).
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
                      (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
  assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
                      page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
  pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
    as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  destruct new as [|p0 new'] eqn:Enew.
  - exists (m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true.
    2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
    exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs ACFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs ACFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Theorem mi_account_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists mat',
    mi_account_step segs ms model
      = MachineOk (unrestrict H (ms_mem ms) msr',
                   with_vm_backing (m_vm_lazy model) mat' model)
    /\ MInv A (with_vm_backing (m_vm_lazy model) mat' model)
    /\ hclean H msr'.
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
    as (mat' & Hmat & Hinv').
  exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
  split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.

(* [comment removed for export] *)
Lemma sstep_instr_det : forall ms model ms1 model1 e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms1, model1) ->
  sstep segs (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms1 model1).
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss.
  inversion Hss; subst;
    match goal with
    | Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
    | Ha : mi_account_step segs ms model = _ |- _ =>
        rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
    end.
Qed.

(* [comment removed for export] *)
Theorem node_instr_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists model',
    MInv A model' /\ same_but_materialized model model'
    /\ hclean H msr'
    /\ mi_account_step segs ms model
         = MachineOk (unrestrict H (ms_mem ms) msr', model')
    /\ node_ok (mkCfg ms model) unit (fun _ => [])
               (fun _ => mkCfg (unrestrict H (ms_mem ms) msr') model').
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
    as (mat' & Hacc & Hinv' & Hcl).
  exists (with_vm_backing (m_vm_lazy model) mat' model).
  split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
  split; [exact Hacc|].
  split.
  - intros []. apply sstep_cfg_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt.
    exact (sstep_instr_det ms model _ _ e st Hsvc Hacc (sstep_of_cfg segs ACFG _ _ _ Hss)).
Qed.

(* [comment removed for export] *)
Lemma step_hclean : forall ms ms',
  hclean H ms ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  hclean H ms'.
Proof.
  intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
  destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
  exact Hcl.
Qed.

Lemma msteps_hclean : forall ms ms',
  msteps segs ms ms' -> hclean H ms -> hclean H ms'.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
  - exact Hc.
  - apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.

Lemma unrestrict_munrestrict : forall f g ms',
  unrestrict H (munrestrict H f g) ms' = unrestrict H f ms'.
Proof.
  intros f g ms'. unfold unrestrict. f_equal.
  apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

(* [comment removed for export] *)
Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
  node_ok c unit (fun _ => []) (fun _ => c') ->
  ms_svc_pending (cfg_ms c) = None ->   (* LPS 727298f3: instruction nodes only ([RomBase.sys_rob_instr]) *)
  P c' -> P c.

Theorem rz_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk.
  destruct (node_instr_restricted A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  exact (P_silent1 _ _ Hnode Hsvc (Hk model' Hinv' Hsame)).
Qed.

Theorem rz_msteps_restricted : forall A msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model,
  msr0 = restrict H ms ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
    intros ms model -> Hcov Hwf Hinv Hh Hk.
  - specialize (Hk model Hinv (same_but_materialized_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
    apply (P_silent1 _ _ Hnode Hsvc).
    pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
    + exact Hwf.
    + exact Hinv1.
    + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
    + intros model' Hinv' Hsame'.
      rewrite unrestrict_mem, unrestrict_munrestrict.
      apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
(* [comment removed for export] *)
Theorem rz_msteps_restricted' : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
  apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
  match materialize_model_accesses m accs with
  | Some m' => m'
  | None => m
  end.

Section SyscallNode.
Variable segs : list Segment.
Variable H : word -> bool.

(* [comment removed for export] *)
Theorem node_syscall_restricted :
  forall A ms model x8 (I : Type)
         (eff : I -> SyscallEffect) (mdl : I -> Model) (evs : I -> list event),
  A_wf A ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (eff i) (mdl i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (eff i)) ->
  (forall r, syscall_spec (sys_input segs ms x8) model r ->
             exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, m_halted (mdl i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (mdl i)) A) ->
  (forall i, MInv A (mdl i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (eff i))) ->
  (forall i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
             /\ same_but_materialized (mdl i)
                  (materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
  /\ node_ok segs (mkCfg ms model) I evs
       (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
                       (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))).
Proof.
  intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hsound Hns Hcompl Hnh Hcov Hinv Hav.
  assert (Hmat : forall i, exists mat',
            materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
              = Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
            /\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
  { intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
  split.
  - intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
    unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
  - split.
    + intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
      unfold materialized_succ. rewrite Hm.
      eapply sstep_cfg_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hns i) | exact (Hnh i) | exact Hm].
    + intros e st Hss. inversion Hss; subst;
        match goal with
        | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
        | Hp : ms_svc_pending ms = Some ?x |- _ =>
            rewrite Hsvc in Hp; injection Hp as <-
        end;
        match goal with
        | Hsp : syscall_spec _ _ ?r |- _ =>
            destruct (Hcompl _ Hsp) as [i Ei]; try discriminate Ei;
            injection Ei as -> -> ->
        end.
      *
        exists i. split; [reflexivity|].
        unfold materialized_succ.
        match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
        reflexivity.
      *
        destruct (Hmat i) as (mat' & Hm & _).
        match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
      *
        match goal with Hc : m_halted (mdl i) = Some _ |- _ => rewrite (Hnh i) in Hc; discriminate end.
      *
        match goal with Hk : m_killed (mdl i) = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh i)) in Hk; discriminate end.
Qed.
End SyscallNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
  fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

Lemma page_in_ranges_incl : forall p l L,
  incl l L -> page_in_ranges p l = true -> page_in_ranges p L = true.
Proof.
  intros p l L Hincl Hp. unfold page_in_ranges in *.
  apply existsb_exists in Hp as (r & Hin & Hr).
  apply existsb_exists. exists r. split; [exact (Hincl r Hin) | exact Hr].
Qed.

Lemma lazy_cover_mkH : forall L A lazy,
  incl lazy L -> lazy_cover (mkH L A) lazy A.
Proof.
  intros L A lazy Hincl w Hl Hw. unfold mkH in Hw.
  rewrite (page_in_ranges_incl _ _ _ Hincl Hl) in Hw. cbn in Hw.
  destruct (page_allowedb A (page_base w)); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition seg_top (seg : Segment) : Z :=
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition wx_segs_nowrap_b (segs : list Segment) : bool :=
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      || (seg_top seg <=? 2 ^ 64)%Z) segs.

Lemma wx_segs_nowrap_of_b : forall segs,
  wx_segs_nowrap_b segs = true -> wx_segs_nowrap segs.
Proof.
  intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
  rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
  apply Z.leb_le in Hb. exact Hb.
Qed.

Definition segs_below_b (segs : list Segment) (top : Z) : bool :=
  forallb (fun seg => (seg_top seg <=? top)%Z) segs.

Lemma find_segment1_none_above : forall segs top x,
  segs_below_b segs top = true -> (top <= x)%Z -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros top x Hb Hx; [reflexivity|].
  cbn [segs_below_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply Z.leb_le in Hs. unfold seg_top in Hs.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z
    with false.
  - exact (IH top x Hl Hx).
  - symmetry. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.

(* [comment removed for export] *)
Lemma H_off_segments_above : forall segs (H : word -> bool) top,
  segs_below_b segs top = true ->
  (forall a, H a = true -> (top <= bv_unsigned a)%Z) ->
  H_off_segments segs H.
Proof.
  intros segs H top Hb Ha a HHa. exact (find_segment1_none_above segs top _ Hb (Ha a HHa)).
Qed.

(* [comment removed for export] *)
Definition ranges_from_b (L : list (word * word)) (top : Z) : bool :=
  forallb (fun r => (top <=? bv_unsigned (fst r))%Z) L.

Lemma page_base_le : forall a, (bv_unsigned (page_base a) <= bv_unsigned a)%Z.
Proof.
  intros a. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hmb.
  assert (Hq : (0 <= bv_unsigned a / page_size)%Z)
    by (apply Z.div_pos; unfold page_size in *; lia).
  set (q := (bv_unsigned a / page_size)%Z) in *.
  change (bv_modulus 64) with (2 ^ 64)%Z in *. unfold page_size in *.
  rewrite bv_wrap_small; [lia|].
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.

Lemma mkH_above : forall L A top a,
  ranges_from_b L top = true -> mkH L A a = true -> (top <= bv_unsigned a)%Z.
Proof.
  intros L A top a Hb Ha. unfold mkH in Ha. apply andb_true_iff in Ha as [Hp _].
  unfold page_in_ranges in Hp. apply existsb_exists in Hp as ([lo sz] & Hin & Hr).
  cbn [fst snd] in Hr. apply andb_true_iff in Hr as [H1 _]. apply Z.leb_le in H1.
  unfold ranges_from_b in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Hin).
  cbn [fst] in Hb. apply Z.leb_le in Hb.
  pose proof (page_base_le a). lia.
Qed.

Corollary H_off_segments_mkH : forall segs L A top,
  segs_below_b segs top = true -> ranges_from_b L top = true ->
  H_off_segments segs (mkH L A).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01Ah12HLh22Hah32Hsh41Lh51ah64segsh73topp;1p;2p;3p;6p;5g00FOj12Tg002kj10Tg003Pj1;Tg003nj14Tg00`aj23Tg05Yhj2<Tg05]Nj2:Tg05Roj25j36Tg05_Ij67Tg05`Cj58Tg004Qj39Tg00Wff0R0g00XF39p=1g01Kh#2g00<D#0#0#0#0#0#0#;#4R1/31#2g00=bR2/32#2f3R3/<0#1f1R4,:3#1f5R5f4R6/53f2R3P4A6560#1f6P5P6P4P3P0E7W2X51D8W1W3X72W0W4W6o"). Qed.

(* [comment removed for export] *)
Lemma MInv_intro_empty : forall A m,
  m_vm_materialized m = [] ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A m.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcct ()) [] "h01ph11lh22Hph31Ah42Hbh52Heh61mp;2p;1p;3p;6p;7g00`aj2HTg00FOj1:Tg002kj10Tg003Pj1>Tg003nj1GTg03:Vj18Tg00Eoj1CTg004Qj33Tg039[j1@Tg03^=j1?Tg006Yj2=Tg03JBj1<Tg04Xdj1;Tg00ESj2FTg040Nj2ETg040jj1DTg00:Bj62Tg00aaj36Tg004kj25Tg00BNj27Tg03hfj24Tg03@Uj1BTg04R5j29Tg04][j7ATg00Wff0R0g00XF33p=1g00=bR1/H1#:g03<3g00<D#0#0#0#0#0#0#>R2#GR3#:R4%80%C3R533f1R6#@f2R7#?'=%<6#;'Ff3P7P4P51E30X14%D3%87R8P6E2P4P5A6306R91526g03<iR:'7g00>_R;531[^03X14A6305R<g00c5R=1527/7:=31;P0n010000000W2X03P8P6E2P4P5f6R;/46#1\9^03X14P=14;7#1P0n010000000X2<X03P8P6E2P4P5f5#BR5,96#1\9^03X14P=1975#1P0n010000000X2<X03P8P6E2P0FAW4W5W6W3o"). Qed.

(* [comment removed for export] *)
Lemma MInv_transport : forall A m m',
  MInv A m ->
  m_vm_materialized m' = m_vm_materialized m ->
  m_vm_lazy m' = m_vm_lazy m ->
  (eager_used m' + A_bytes A <= vm_limit (m_vmmaps m'))%Z ->
  MInv A m'.
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.

