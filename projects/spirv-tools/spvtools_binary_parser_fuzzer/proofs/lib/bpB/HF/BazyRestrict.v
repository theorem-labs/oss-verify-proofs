(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (an instruction fetch at the vDSO text, with proofs written as text in place of recorded proofs, and the model's channel reader kept by materialization). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Ltac flia := solve [ repeat match goal with x := _ |- _ => clearbody x end; lia ].
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BazyRestrict () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions6bv_addK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4succC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC56Stdlib6ZArith4Znat5Nat2Z8inj_succC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedC47Corelib4Init5Logic8eq_ind_rI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC56Stdlib6ZArith6BinInt1Z7add_0_rK47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib3bpB2HF<BazyRestrict<bv_add_nat_0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC46Stdlib9micromega;ZifyClasses7rew_iffc69OSSVerify5KrLib3bpB2HF<BazyRestrict<bv_add_nat_SC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c69OSSVerify5KrLib3bpB2HF<BazyRestrict=range_visibleC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic7f_equalI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic5False00c69OSSVerify5KrLib3bpB2HF<BazyRestrictAfind_segment_specC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict:seg_coversC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib7Numbers7BinNums8positive01c69OSSVerify5KrLib3bpB2HF<BazyRestrictEbv_unsigned_add_smallC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictDfind_segment_visibleC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atc69OSSVerify5KrLib3bpB2HF<BazyRestrictEfind_segment_visible1C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readc69OSSVerify5KrLib3bpB2HF<BazyRestrictCmemory_read1_hiddenC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict7ov_byteC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK46Stdlib9micromega5Tauto8GFormula03c69OSSVerify5KrLib3bpB2HF<BazyRestrictDov_read_bytes_unfoldC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict@ov_byte_restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict?range_visible_SC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc69OSSVerify5KrLib3bpB2HF<BazyRestrict>wview_restrictC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityI47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00I47Corelib4Init5Logic2ex00K4ELinuxProcessSemantics5Riscv3Sem3eff01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01c69OSSVerify5KrLib3bpB2HF<BazyRestrict>ranges_visibleC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K47Corelib4Init5Logic2ex01K4ELinuxProcessSemantics5Riscv3Sem3eff02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03K4ELinuxProcessSemantics5Riscv3Sem3eff03K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics5Riscv3Sem3eff04K4ELinuxProcessSemantics5Riscv3Sem3eff05K4ELinuxProcessSemantics5Riscv3Sem3eff06K4ELinuxProcessSemantics5Riscv3Sem3eff07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;width_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesc69OSSVerify5KrLib3bpB2HF<BazyRestrictFov_read_bytes_restrictC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv3Sem3eff08c69OSSVerify5KrLib3bpB2HF<BazyRestrictAstore_ok_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBaseDlength_Z_to_le_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc69OSSVerify5KrLib3bpB2HF<BazyRestrictEwrite_to_mem_restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictCwrite_to_mem_hiddenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7eff_indK47Corelib4Init9Datatypes4prod01C45stdpp9bitvector;definitions:bv_extractI4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem3eff00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsAseg_ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executableC46Stdlib6ZArith4Znat7N_nat_Zc69OSSVerify5KrLib3bpB2HF<BazyRestrictJseg_ov_read_bytes_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<code_read_ovC47Corelib4Init9Datatypes4negbC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le4c69OSSVerify5KrLib3bpB2HF<BazyRestrictEcode_read_ov_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem6BvBase3le2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_half_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_halfc69OSSVerify5KrLib3bpB2HF<BazyRestrictFfetch_half_ov_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_half_anyC4ELinuxProcessSemantics5Riscv7Prelude4bitsC45stdpp9bitvector;definitions9bv_concatc69OSSVerify5KrLib3bpB2HF<BazyRestrictGfetch_half_any_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@fetch_byte_trapsC47Corelib4Init9Datatypes3orbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c69OSSVerify5KrLib3bpB2HF<BazyRestrict;restrict_byC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01C4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalc69OSSVerify5KrLib3bpB2HF<BazyRestrict8lifts_toC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict?restrict_mem_byC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict=unrestrict_byC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictAunrestrict_mem_byC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingc69OSSVerify5KrLib3bpB2HF<BazyRestrictLinterp_eff_accesses_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics5Riscv3Sem4execI4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordc69OSSVerify5KrLib3bpB2HF<BazyRestrictMdecode_exec_accesses_restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictFfetch_word_ov_restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictGfetch_tail_any_restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictFfetch_failure_restrictC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_step_accessesc69OSSVerify5KrLib3bpB2HF<BazyRestrictFstep_accesses_restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict<segs_nowrapbC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool;andb_true_rc69OSSVerify5KrLib3bpB2HF<BazyRestrict>lazy_range_okbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbc69OSSVerify5KrLib3bpB2HF<BazyRestrict?lazy_ranges_okbC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init5Logic7and_indC47Corelib4Init9Datatypes8prod_indC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List;forallb_appC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallc69OSSVerify5KrLib3bpB2HF<BazyRestrict:zin_rangebC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndc69OSSVerify5KrLib3bpB2HF<BazyRestrict:in_rangesbC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notc69OSSVerify5KrLib3bpB2HF<BazyRestrict?in_rangesb_trueC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict7hiddenbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict?hid_avoids_segsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict=range_nowrapbC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictCseg_disjoint_rangebC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffC46Stdlib4Bool4Bool=negb_true_iffc69OSSVerify5KrLib3bpB2HF<BazyRestrict8restrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictElazy_ranges_ok_avoidsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict@step_restrict_byC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictFrestrict_unrestrict_byC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictBunrestrict_by_idemC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc69OSSVerify5KrLib3bpB2HF<BazyRestrict5cl_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict5cl_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict;win_npagesZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib6ZArith4Zdiv:Z_mod_multK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z7div_mulK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec69OSSVerify5KrLib3bpB2HF<BazyRestrict;pages_totalC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict9cl_boundsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02c69OSSVerify5KrLib3bpB2HF<BazyRestrict7wbudgetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict9all_pagesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict9win_pagesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addc69OSSVerify5KrLib3bpB2HF<BazyRestrict:win_npagesC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Z2Nat2idC46Stdlib5Lists4List:length_seqc69OSSVerify5KrLib3bpB2HF<BazyRestrict8win_pageC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List:length_appc69OSSVerify5KrLib3bpB2HF<BazyRestrict:eager_usedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c69OSSVerify5KrLib3bpB2HF<BazyRestrictEsame_but_materializedC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingI4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z7mod_addC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofc69OSSVerify5KrLib3bpB2HF<BazyRestrictGbv_unsigned_add_Z_to_bvC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictEpage_base_of_unsignedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z<eq_decidableC56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z7div_addC46Stdlib5Lists4List:in_map_iffI47Corelib4Init5Peano2le00C46Stdlib5Lists4List6in_seqC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List8map_consC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC56Stdlib6ZArith6BinInt1Z8eqb_reflC4ELinuxProcessSemantics?LinuxProcessSem5State8page_memC4ELinuxProcessSemantics?LinuxProcessSem5State;page_insertI46Stdlib5Lists4List5NoDup00c69OSSVerify5KrLib3bpB2HF<BazyRestrict;page_mem_InC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List5NoDup02C4ELinuxProcessSemantics?LinuxProcessSem5State@access_pages_accc69OSSVerify5KrLib3bpB2HF<BazyRestrictANoDup_page_insertC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>accesses_pagesc69OSSVerify5KrLib3bpB2HF<BazyRestrictFNoDup_access_pages_accC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict>page_insert_inC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega8ZifyInst7Inj_Z_Zc69OSSVerify5KrLib3bpB2HF<BazyRestrictCaccess_pages_acc_inC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List4inclK46Stdlib5Lists4List5NoDup01c69OSSVerify5KrLib3bpB2HF<BazyRestrictDNoDup_accesses_pagesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<NoDup_filterC46Stdlib5Lists4List9filter_Inc69OSSVerify5KrLib3bpB2HF<BazyRestrictAaccesses_pages_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictCpage_of_access_byteC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictHwindow_page_in_all_pagesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictCpage_in_ranges_addrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateHnewly_materialized_pagesi69OSSVerify5KrLib3bpB2HF<BazyRestrict8lazy_inv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesc69OSSVerify5KrLib3bpB2HF<BazyRestrictPnewly_materialized_pages_visibleC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9NoDup_appC46Stdlib5Lists4List8incl_appC46Stdlib5Lists4ListANoDup_incl_lengthc69OSSVerify5KrLib3bpB2HF<BazyRestrict@all_pages_lengthC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>vm_backed_mapsC4ELinuxProcessSemantics?LinuxProcessSem5StateAmaps_subtract_allC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitk69OSSVerify5KrLib3bpB2HF<BazyRestrict8lazy_inv01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedc69OSSVerify5KrLib3bpB2HF<BazyRestrictEvm_backing_used_splitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict=unrestrict_toC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9incl_tranC46Stdlib5Lists4List9incl_reflC46Stdlib5Lists4List9incl_apprc69OSSVerify5KrLib3bpB2HF<BazyRestrictElazy_inv_windows_monoC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;existsb_appc69OSSVerify5KrLib3bpB2HF<BazyRestrict?in_rangesb_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictChiddenb_cons_windowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict<restrict_memC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictHrestrict_mem_open_windowC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrict8with_memC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC56Stdlib6ZArith6BinInt1Z7add_modC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z8le_max_lC56Stdlib6ZArith6BinInt1Z8le_max_rC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes>Morphisms_Prop?or_iff_morphismc69OSSVerify5KrLib3bpB2HF<BazyRestrictClazy_ranges_okb_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictDlazy_ranges_okb_consC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictClazy_ranges_okb_appC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictBiv_subtract_withinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF<BazyRestrictElazy_range_okb_withinC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition zin_rangeb (z : Z) (r : word * word) : bool :=
  ((bv_unsigned (fst r) <=? z) && (z <? bv_unsigned (fst r) + bv_unsigned (snd r)))%Z.

Definition in_rangesb (a : word) (rs : list (word * word)) : bool :=
  existsb (zin_rangeb (bv_unsigned a)) rs.

Definition hiddenb (L S : list (word * word)) (a : word) : bool :=
  in_rangesb a L && negb (in_rangesb a S).

Definition restrict_mem_by (hid : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if hid a then None else m a.

Definition unrestrict_mem_by (hid : word -> bool) (mF m1 : word -> option byte)
    : word -> option byte :=
  fun a => if hid a then mF a else m1 a.

Definition with_mem (ms : machine_state) (m : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := m; ms_rom := ms_rom ms |}.

Definition restrict_by (hid : word -> bool) (ms : machine_state) : machine_state :=
  with_mem ms (restrict_mem_by hid (ms_mem ms)).

Definition unrestrict_by (hid : word -> bool) (msF ms1 : machine_state) : machine_state :=
  with_mem ms1 (unrestrict_mem_by hid (ms_mem msF) (ms_mem ms1)).

Definition restrict_mem (L S : list (word * word)) := restrict_mem_by (hiddenb L S).
Definition restrict (L S : list (word * word)) := restrict_by (hiddenb L S).
Definition unrestrict_to (L S : list (word * word)) := unrestrict_by (hiddenb L S).

Definition range_visible (hid : word -> bool) (a : word) (n : nat) : Prop :=
  forall i, (i < n)%nat -> hid (a + Z_to_bv 64 (Z.of_nat i)) = false.

Definition ranges_visible (hid : word -> bool) (rs : list memory_access) : Prop :=
  forall a n, In (a, n) rs -> range_visible hid a n.

Definition seg_covers (seg : Segment) (z : Z) : Prop :=
  (Z.of_N (seg_base seg) <= z < Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition hid_avoids_segs (segs : list Segment) (hid : word -> bool) : Prop :=
  (forall a seg, In seg segs -> seg_covers seg (bv_unsigned a) -> hid a = false)
  /\ (forall seg, In seg segs ->
        (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z).

Lemma bv_add_nat_S : forall (a : word) i,
  a + Z_to_bv 64 (Z.of_nat (S i)) = (a + 1) + Z_to_bv 64 (Z.of_nat i).
Proof.
  intros a i. apply bv_eq.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  unfold bv_wrap. rewrite Nat2Z.inj_succ.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
  f_equal. lia.
Qed.

Lemma bv_add_nat_0 : forall (a : word), a + Z_to_bv 64 (Z.of_nat 0) = a.
Proof.
  intros a. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 (Z.of_nat 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma bv_unsigned_add_small : forall (a : word) (i : Z),
  (0 <= i)%Z -> (bv_unsigned a + i < 2 ^ 64)%Z ->
  bv_unsigned (a + Z_to_bv 64 i) = (bv_unsigned a + i)%Z.
Proof.
  intros a i Hi Hlt.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  change (bv_modulus 64) with (2^64)%Z in Ha.
  rewrite bv_add_unsigned, Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 i) by (change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma range_visible_S : forall hid a n,
  range_visible hid a (S n) <-> hid a = false /\ range_visible hid (a + 1) n.
Proof.
  intros hid a n. unfold range_visible. split.
  - intros H. split.
    + rewrite <- (bv_add_nat_0 a). apply H. lia.
    + intros i Hi. rewrite <- bv_add_nat_S. apply H. lia.
  - intros [H0 HS] i Hi. destruct i as [|i].
    + rewrite bv_add_nat_0. exact H0.
    + rewrite bv_add_nat_S. apply HS. lia.
Qed.

Section HidSem.
Variable segs : list Segment.
Variable hid : word -> bool.
Hypothesis Hhs : hid_avoids_segs segs hid.

Let rmem := restrict_mem_by hid.

Lemma find_segment_spec : forall ss z n seg,
  find_segment ss z n = Some seg ->
  In seg ss /\ (Z.of_N (seg_base seg) <= z)%Z
  /\ (z + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction ss as [|s ss IH]; cbn; intros z n seg H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s)) z && Z.leb (z + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - inversion H; subst. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. auto.
  - destruct (IH z n seg H) as (Hin & H1 & H2). auto.
Qed.

Lemma find_segment_visible : forall a n seg,
  find_segment segs (bv_unsigned a) (Z.of_nat n) = Some seg ->
  range_visible hid a n.
Proof.
  intros a n seg Hf i Hi.
  destruct (find_segment_spec _ _ _ _ Hf) as (Hin & Hlo & Hhi).
  destruct Hhs as [Hcov Hnw].
  pose proof (Hnw seg Hin) as Hseg.
  apply (Hcov _ seg Hin). unfold seg_covers.
  rewrite bv_unsigned_add_small by lia. lia.
Qed.

Lemma find_segment_visible1 : forall a seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> hid a = false.
Proof.
  intros a seg Hf.
  rewrite <- (bv_add_nat_0 a).
  apply (find_segment_visible a 1 seg); [exact Hf | lia].
Qed.

Lemma wview_restrict : forall m a,
  wview segs (rmem m) a = if hid a then None else wview segs m a.
Proof.
  intros m a. unfold wview, rmem, restrict_mem_by.
  destruct (hid a) eqn:Eh; [|reflexivity].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|reflexivity].
  pose proof (find_segment_visible1 a seg Ef). congruence.
Qed.

Lemma memory_read1_hidden : forall a,
  hid a = true ->
  match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end = None.
Proof.
  intros a Ha. unfold memory_read. change (Z.of_N 1) with 1%Z.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Ef; [|reflexivity].
  pose proof (find_segment_visible1 a seg Ef). congruence.
Qed.

Definition ov_byte (m : word -> option byte) (a : word) : option byte :=
  match m a with
  | Some b => Some b
  | None => match memory_read segs a 1 with
            | Some (b :: _) => Some b
            | _ => None
            end
  end.

Lemma ov_byte_restrict : forall m a,
  ov_byte (rmem m) a = if hid a then None else ov_byte m a.
Proof.
  intros m a. unfold ov_byte, rmem, restrict_mem_by.
  destruct (hid a) eqn:Eh; [|reflexivity].
  exact (memory_read1_hidden a Eh).
Qed.

Lemma ov_read_bytes_unfold : forall m a n,
  ov_read_bytes segs m a (S n) =
  match ov_byte m a with
  | Some b => match ov_read_bytes segs m (a + 1) n with
              | Some rest => Some (b :: rest) | None => None end
  | None => None
  end.
Proof.
 reflexivity. Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
  ov_read_bytes segs (rmem m) a n = Some bs ->
  ov_read_bytes segs m a n = Some bs /\ range_visible hid a n.
Proof.
  induction n as [|n IH]; intros m a bs H.
  - cbn in H |- *. split; [exact H|]. intros i Hi. lia.
  - rewrite ov_read_bytes_unfold in H |- *. rewrite ov_byte_restrict in H.
    destruct (hid a) eqn:Eh; [discriminate|].
    destruct (ov_byte m a) as [b|]; [|discriminate].
    destruct (ov_read_bytes segs (rmem m) (a + 1) n) as [rest|] eqn:Er; [|discriminate].
    destruct (IH m (a + 1) rest Er) as [-> Hvis].
    split; [exact H|].
    apply range_visible_S. split; [exact Eh | exact Hvis].
Qed.

Lemma store_ok_restrict : forall n m a,
  store_ok segs (rmem m) a n = true ->
  store_ok segs m a n = true /\ range_visible hid a n.
Proof.
  induction n as [|n IH]; intros m a H.
  - split; [reflexivity|]. intros i Hi. lia.
  - cbn [store_ok] in H |- *. rewrite wview_restrict in H.
    destruct (hid a) eqn:Eh; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) H) as [-> Hvis].
    split; [reflexivity|].
    apply range_visible_S. split; [exact Eh | exact Hvis].
Qed.

Lemma write_to_mem_restrict : forall data m a,
  range_visible hid a (length data) ->
  write_to_mem (rmem m) a data = rmem (write_to_mem m a data).
Proof.
  induction data as [|b data IH]; intros m a Hvis; cbn [write_to_mem length] in *.
  - reflexivity.
  - apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
    rewrite <- (IH _ (a + 1) Hvis). f_equal.
    apply functional_extensionality. intros x.
    unfold rmem, restrict_mem_by.
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
    rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : forall data m a x,
  range_visible hid a (length data) ->
  hid x = true ->
  write_to_mem m a data x = m x.
Proof.
  induction data as [|b data IH]; intros m a x Hvis Hx; cbn [write_to_mem length] in *.
  - reflexivity.
  - apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
    rewrite (IH _ (a + 1) x Hvis Hx).
    destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x. congruence.
Qed.

Lemma interp_eff_accesses_restrict : forall t m c m1 rs,
  interp_eff_accesses segs t (rmem m) = MachineOk (@mkAccessReport _ (c, m1) rs) ->
  exists m',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, m') rs)
    /\ m1 = rmem m'
    /\ (forall x, hid x = true -> m' x = m x)
    /\ ranges_visible hid rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mres rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    intros a0 n0 Hin. destruct Hin.
  - destruct (ov_read_bytes segs (rmem m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [| destruct (range_meets_vvar segs a (width_bytes n)); discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (rmem m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    intros a0 n0 Hin. destruct Hin as [E | Hin].
    + injection E as E1 E2. subst. exact Hav.
    + exact (Hrs _ _ Hin).
  - destruct (store_ok segs (rmem m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (rmem (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + intros a0 n0 Hin. destruct Hin as [E | Hin].
      * injection E as E1 E2. subst. exact Hav.
      * exact (Hrs _ _ Hin).
Qed.

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
  range_visible hid a n ->
  seg_ov_read_bytes (rmem m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
  induction n as [|n IH]; intros m seg a Hvis; [reflexivity|].
  cbn [seg_ov_read_bytes].
  apply range_visible_S in Hvis. destruct Hvis as [Ha Hvis].
  unfold rmem at 1, restrict_mem_by. rewrite Ha. fold rmem.
  rewrite (IH m seg (a + 1) Hvis). reflexivity.
Qed.

Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (rmem m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Ef; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg); [|reflexivity].
  apply seg_ov_read_bytes_restrict.
  apply (find_segment_visible a (N.to_nat n) seg).
  rewrite N_nat_Z. exact Ef.
Qed.

Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (rmem m) a = fetch_word_ov segs m a.
Proof.
 intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (rmem m) a = fetch_half_ov segs m a.
Proof.
 intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (rmem m) a = fetch_half_any segs m a.
Proof.
 intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (rmem m) a = fetch_tail_any segs m a.
Proof.
 intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (rmem m) a = fetch_failure segs m a.
Proof.
(* plain proof: at 08b1429 [fetch_failure] first tests [vdso_text_at]
   (segs only), then reads memory only through [fetch_half_any] *)
  intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity.
Qed.

Definition lifts_to (msF : machine_state) (rep1 : access_report machine_state)
    (res : machine_result (access_report machine_state)) : Prop :=
  exists rep,
    res = MachineOk rep
    /\ accessed_ranges _ rep = accessed_ranges _ rep1
    /\ access_value _ rep = unrestrict_by hid msF (access_value _ rep1)
    /\ ranges_visible hid (accessed_ranges _ rep1)
    /\ (forall x, hid x = true -> ms_mem (access_value _ rep1) x = None)
    /\ (forall x, hid x = true -> ms_mem (access_value _ rep) x = ms_mem msF x).

Lemma decode_exec_accesses_restrict : forall msF w rep1,
  decode_exec_accesses segs (restrict_by hid msF) w = MachineOk rep1 ->
  lifts_to msF rep1 (decode_exec_accesses segs msF w).
Proof.
  intros msF w rep1 H. unfold decode_exec_accesses in H |- *.
  destruct (is_ecall w).
  - inversion H; subst; clear H. eexists. split; [reflexivity|].
    cbn. split; [reflexivity|]. split; [|split; [|split]].
    + unfold unrestrict_by, with_mem. cbn. f_equal.
      apply functional_extensionality. intros x.
      unfold unrestrict_mem_by, restrict_mem_by. destruct (hid x); reflexivity.
    + intros a n [].
    + intros x Hx. unfold restrict_mem_by. rewrite Hx. reflexivity.
    + intros x Hx. reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [restrict_by with_mem ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom] in H.
    destruct (interp_eff_accesses segs (exec (Z_to_bv 64 isz) i
                {| c_regs := ms_regs msF; c_fregs := ms_fregs msF; c_pc := ms_pc_val msF;
                   c_fcsr := ms_fcsr msF; c_resv := ms_resv msF |})
                (restrict_mem_by hid (ms_mem msF)))
      as [[[c m1] rs]| |] eqn:Ei; [|discriminate|discriminate].
    cbn in H. inversion H; subst; clear H.
    destruct (interp_eff_accesses_restrict _ _ _ _ _ Ei) as (m' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn. eexists. split; [reflexivity|].
    cbn. split; [reflexivity|]. split; [|split; [|split]].
    + unfold unrestrict_by, with_mem. cbn. f_equal.
      apply functional_extensionality. intros x.
      unfold unrestrict_mem_by, restrict_mem_by.
      unfold rmem, restrict_mem_by.
      destruct (hid x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + exact Hrs.
    + intros x Hx. unfold rmem, restrict_mem_by. rewrite Hx. reflexivity.
    + exact Hhid.
Qed.

Lemma step_accesses_restrict : forall msF rep1,
  step_accesses segs (restrict_by hid msF) = MachineOk rep1 ->
  lifts_to msF rep1 (step_accesses segs msF).
Proof.
  intros msF rep1 H. unfold step_accesses in H |- *.
  change (ms_pc (restrict_by hid msF)) with (ms_pc msF) in H.
  change (ms_mem (restrict_by hid msF)) with (rmem (ms_mem msF)) in H.
  destruct (fetch_word segs (ms_pc msF)) as [w|].
  { exact (decode_exec_accesses_restrict _ _ _ H). }
  rewrite fetch_word_ov_restrict in H.
  destruct (fetch_word_ov segs (ms_mem msF) (ms_pc msF)) as [w|].
  { exact (decode_exec_accesses_restrict _ _ _ H). }
  rewrite fetch_tail_any_restrict in H.
  destruct (fetch_tail_any segs (ms_mem msF) (ms_pc msF)) as [w|].
  { exact (decode_exec_accesses_restrict _ _ _ H). }
  rewrite fetch_failure_restrict in H.
  unfold fetch_failure in H |- *.
  destruct (vdso_text_at segs (ms_pc msF)); [discriminate|].
  destruct (negb (bv_unsigned (ms_pc msF) `mod` 2 =? 0)%Z); [discriminate|].
  match type of H with (match (if ?c then _ else _) with _ => _ end = _) =>
    destruct c; discriminate end.
Qed.

Theorem step_restrict_by : forall msF ms1,
  RiscvSemantics.step segs (restrict_by hid msF) = MachineOk ms1 ->
  exists rep,
    step_accesses segs msF = MachineOk rep
    /\ access_value _ rep = unrestrict_by hid msF ms1
    /\ ranges_visible hid (accessed_ranges _ rep)
    /\ (forall x, hid x = true -> ms_mem ms1 x = None)
    /\ (forall x, hid x = true -> ms_mem (access_value _ rep) x = ms_mem msF x).
Proof.
  intros msF ms1 H.
  rewrite <- drop_step_accesses in H.
  destruct (step_accesses segs (restrict_by hid msF)) as [rep1| |] eqn:E1;
    cbn in H; [|discriminate|discriminate].
  inversion H; subst; clear H.
  destruct (step_accesses_restrict _ _ E1) as (rep & -> & Hrs & Hval & Hvis & Hnone & Hhid).
  exists rep. split; [reflexivity|]. split; [exact Hval|].
  split; [rewrite Hrs; exact Hvis|]. split; [exact Hnone | exact Hhid].
Qed.

Lemma restrict_unrestrict_by : forall msF ms1,
  (forall x, hid x = true -> ms_mem ms1 x = None) ->
  restrict_by hid (unrestrict_by hid msF ms1) = ms1.
Proof.
  intros msF [regs fregs pc svc resv fcsr m rom] Hnone.
  unfold restrict_by, unrestrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros x.
  unfold restrict_mem_by, unrestrict_mem_by. cbn in Hnone.
  destruct (hid x) eqn:Hx; [symmetry; exact (Hnone x Hx) | reflexivity].
Qed.

Lemma unrestrict_by_hidden : forall msF ms1 x,
  hid x = true -> ms_mem (unrestrict_by hid msF ms1) x = ms_mem msF x.
Proof.
  intros msF ms1 x Hx. unfold unrestrict_by, with_mem, unrestrict_mem_by. cbn.
  rewrite Hx. reflexivity.
Qed.

Lemma unrestrict_by_idem : forall msF ms1 ms2,
  unrestrict_by hid (unrestrict_by hid msF ms1) ms2 = unrestrict_by hid msF ms2.
Proof.
  intros msF ms1 ms2. unfold unrestrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros x. unfold unrestrict_mem_by.
  destruct (hid x); reflexivity.
Qed.

End HidSem.

Definition seg_disjoint_rangeb (seg : Segment) (r : word * word) : bool :=
  let sb := Z.of_N (seg_base seg) in
  let se := (sb + Z.of_N (seg_size seg))%Z in
  let lo := bv_unsigned (fst r) in
  let hi := (lo + bv_unsigned (snd r))%Z in
  ((se <=? lo) || (hi <=? sb))%Z.

Definition segs_nowrapb (segs : list Segment) : bool :=
  forallb (fun seg => (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 2 ^ 64)%Z) segs.

Definition range_nowrapb (r : word * word) : bool :=
  (bv_unsigned (fst r) + bv_unsigned (snd r) <=? 2 ^ 64)%Z.

Definition lazy_range_okb (segs : list Segment) (r : word * word) : bool :=
  range_nowrapb r && forallb (fun seg => seg_disjoint_rangeb seg r) segs.

Definition lazy_ranges_okb (segs : list Segment) (L : list (word * word)) : bool :=
  segs_nowrapb segs && forallb (lazy_range_okb segs) L.

Lemma lazy_ranges_okb_nil : forall segs, lazy_ranges_okb segs [] = segs_nowrapb segs.
Proof.
 intros segs. unfold lazy_ranges_okb. cbn. apply andb_true_r. Qed.

Lemma lazy_ranges_okb_cons : forall segs r L,
  lazy_ranges_okb segs (r :: L) = true <->
  lazy_range_okb segs r = true /\ lazy_ranges_okb segs L = true.
Proof.
  intros segs r L. unfold lazy_ranges_okb. cbn [forallb].
  rewrite !andb_true_iff. tauto.
Qed.

Lemma lazy_ranges_okb_app : forall segs L1 L2,
  lazy_ranges_okb segs (L1 ++ L2) = true <->
  lazy_ranges_okb segs L1 = true /\ lazy_ranges_okb segs L2 = true.
Proof.
  intros segs L1 L2. unfold lazy_ranges_okb. rewrite forallb_app, !andb_true_iff. tauto.
Qed.

Lemma lazy_ranges_okb_In : forall segs L r,
  lazy_ranges_okb segs L = true -> In r L -> lazy_range_okb segs r = true.
Proof.
  intros segs L r H Hin. unfold lazy_ranges_okb in H. apply andb_true_iff in H.
  destruct H as [_ H]. rewrite forallb_forall in H. exact (H r Hin).
Qed.

Lemma in_rangesb_true : forall a rs,
  in_rangesb a rs = true <->
  exists lo sz, In (lo, sz) rs
    /\ (bv_unsigned lo <= bv_unsigned a < bv_unsigned lo + bv_unsigned sz)%Z.
Proof.
  intros a rs. unfold in_rangesb. rewrite existsb_exists. split.
  - intros ([lo sz] & Hin & Hr). unfold zin_rangeb in Hr. cbn [fst snd] in Hr.
    apply andb_true_iff in Hr. destruct Hr as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists lo, sz. auto.
  - intros (lo & sz & Hin & Hr). exists (lo, sz). split; [exact Hin|].
    unfold zin_rangeb. cbn [fst snd]. apply andb_true_iff. split;
      [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_rangesb_false : forall a rs,
  in_rangesb a rs = false <->
  forall lo sz, In (lo, sz) rs ->
    ~ (bv_unsigned lo <= bv_unsigned a < bv_unsigned lo + bv_unsigned sz)%Z.
Proof.
  intros a rs. split.
  - intros Hf lo sz Hin Hr.
    assert (Ht : in_rangesb a rs = true) by (apply in_rangesb_true; eauto).
    congruence.
  - intros H. destruct (in_rangesb a rs) eqn:E; [|reflexivity].
    apply in_rangesb_true in E. destruct E as (lo & sz & Hin & Hr).
    exfalso. exact (H lo sz Hin Hr).
Qed.

Lemma lazy_ranges_ok_avoids : forall segs L S,
  lazy_ranges_okb segs L = true -> hid_avoids_segs segs (hiddenb L S).
Proof.
  intros segs L S Hok. unfold lazy_ranges_okb in Hok. apply andb_true_iff in Hok.
  destruct Hok as [Hnw HL]. unfold segs_nowrapb in Hnw.
  rewrite forallb_forall in Hnw. rewrite forallb_forall in HL.
  split.
  - intros a seg Hin Hcov.
    unfold hiddenb. destruct (in_rangesb a L) eqn:EL; [|reflexivity].
    apply in_rangesb_true in EL. destruct EL as (lo & sz & HinL & Hr).
    specialize (HL (lo, sz) HinL). unfold lazy_range_okb in HL.
    apply andb_true_iff in HL. destruct HL as [_ HL]. rewrite forallb_forall in HL.
    specialize (HL seg Hin). unfold seg_disjoint_rangeb in HL. cbn [fst snd] in HL.
    unfold seg_covers in Hcov. apply orb_true_iff in HL.
    destruct HL as [Hd|Hd]; apply Z.leb_le in Hd; exfalso; lia.
  - intros seg Hin. specialize (Hnw seg Hin). apply Z.leb_le in Hnw. exact Hnw.
Qed.

Lemma hiddenb_true_iff : forall L S a,
  hiddenb L S a = true <-> in_rangesb a L = true /\ in_rangesb a S = false.
Proof.
  intros L S a. unfold hiddenb. rewrite andb_true_iff, negb_true_iff. tauto.
Qed.

Theorem step_restrict : forall segs L S msF ms1,
  lazy_ranges_okb segs L = true ->
  RiscvSemantics.step segs (restrict L S msF) = MachineOk ms1 ->
  exists rep,
    step_accesses segs msF = MachineOk rep
    /\ access_value _ rep = unrestrict_to L S msF ms1
    /\ ranges_visible (hiddenb L S) (accessed_ranges _ rep)
    /\ (forall a, hiddenb L S a = true -> ms_mem ms1 a = None)
    /\ (forall a, hiddenb L S a = true -> ms_mem (access_value _ rep) a = ms_mem msF a).
Proof.
  intros segs L S msF ms1 Hok Hstep.
  exact (step_restrict_by segs (hiddenb L S) (lazy_ranges_ok_avoids segs L S Hok) msF ms1 Hstep).
Qed.

Lemma restrict_unrestrict_to : forall L S msF ms1,
  (forall a, hiddenb L S a = true -> ms_mem ms1 a = None) ->
  restrict L S (unrestrict_to L S msF ms1) = ms1.
Proof.
 intros L S. exact (restrict_unrestrict_by (hiddenb L S)). Qed.

Lemma unrestrict_to_idem : forall L S msF ms1 ms2,
  unrestrict_to L S (unrestrict_to L S msF ms1) ms2 = unrestrict_to L S msF ms2.
Proof.
 intros L S. exact (unrestrict_by_idem (hiddenb L S)). Qed.

Definition page_alignedb (r : word * word) : bool :=
  ((bv_unsigned (fst r) mod page_size =? 0) && (bv_unsigned (snd r) mod page_size =? 0))%Z.

Definition windows_okb (S : list (word * word)) : bool := forallb page_alignedb S.

Definition cl_lo (r : word * word) : Z := (bv_unsigned (fst r) / page_size * page_size)%Z.
Definition cl_hi (r : word * word) : Z :=
  ((bv_unsigned (fst r) + bv_unsigned (snd r) + page_size - 1) / page_size * page_size)%Z.
Definition win_npagesZ (r : word * word) : Z := ((cl_hi r - cl_lo r) / page_size)%Z.

Lemma cl_bounds : forall r,
  (0 <= cl_lo r <= bv_unsigned (fst r))%Z
  /\ (bv_unsigned (fst r) + bv_unsigned (snd r) <= cl_hi r < bv_unsigned (fst r) + bv_unsigned (snd r) + page_size)%Z
  /\ (cl_lo r mod page_size = 0)%Z /\ (cl_hi r mod page_size = 0)%Z
  /\ (0 <= win_npagesZ r <= bv_unsigned (snd r) / page_size + 2)%Z
  /\ (win_npagesZ r * page_size = cl_hi r - cl_lo r)%Z.
Proof.
  intros [b n]. unfold win_npagesZ, cl_lo, cl_hi. cbn [fst snd].
  pose proof (bv_unsigned_in_range 64 b) as Hb. pose proof (bv_unsigned_in_range 64 n) as Hn.
  set (lo := bv_unsigned b) in *. set (sz := bv_unsigned n) in *.
  pose proof (Z.div_mod lo page_size ltac:(unfold page_size; lia)) as D1.
  pose proof (Z.mod_pos_bound lo page_size ltac:(unfold page_size; lia)) as M1.
  pose proof (Z.div_mod (lo + sz + page_size - 1) page_size ltac:(unfold page_size; lia)) as D2.
  pose proof (Z.mod_pos_bound (lo + sz + page_size - 1) page_size ltac:(unfold page_size; lia)) as M2.
  pose proof (Z.div_mod sz page_size ltac:(unfold page_size; lia)) as D3.
  pose proof (Z.mod_pos_bound sz page_size ltac:(unfold page_size; lia)) as M3.
  set (q1 := (lo / page_size)%Z) in *. set (q2 := ((lo + sz + page_size - 1) / page_size)%Z) in *.
  set (q3 := (sz / page_size)%Z) in *.
  replace (q2 * page_size - q1 * page_size)%Z with ((q2 - q1) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  unfold page_size in *.
  repeat split; first [apply Z_mod_mult | lia].
Qed.

Definition win_npages (r : word * word) : nat := Z.to_nat (win_npagesZ r).

Definition win_page (r : word * word) (i : nat) : word :=
  Z_to_bv 64 (cl_lo r + page_size * Z.of_nat i).

Definition win_pages (r : word * word) : list word :=
  map (win_page r) (seq 0 (win_npages r)).

Fixpoint all_pages (S : list (word * word)) : list word :=
  match S with
  | [] => []
  | r :: S' => win_pages r ++ all_pages S'
  end.

Fixpoint pages_total (S : list (word * word)) : Z :=
  match S with
  | [] => 0
  | r :: S' => win_npagesZ r + pages_total S'
  end%Z.

Fixpoint wbudget (S : list (word * word)) : Z :=
  match S with
  | [] => 0
  | r :: S' => bv_unsigned (snd r) / page_size + 2 + wbudget S'
  end%Z.

Lemma pages_total_nonneg : forall S, (0 <= pages_total S)%Z.
Proof.
  induction S as [|r S IH]; cbn [pages_total]; [lia|].
  destruct (cl_bounds r) as (_ & _ & _ & _ & Hn & _). lia.
Qed.

Lemma pages_total_le_wbudget : forall S, (pages_total S <= wbudget S)%Z.
Proof.
  induction S as [|r S IH]; cbn [pages_total wbudget]; [lia|].
  destruct (cl_bounds r) as (_ & _ & _ & _ & Hn & _). lia.
Qed.

Lemma all_pages_length : forall S,
  Z.of_nat (length (all_pages S)) = pages_total S.
Proof.
  induction S as [|r S IH]; cbn [all_pages pages_total length]; [reflexivity|].
  rewrite length_app, Nat2Z.inj_add, IH. unfold win_pages.
  rewrite length_map, length_seq. unfold win_npages.
  pose proof (cl_bounds r). rewrite Z2Nat.id by lia. reflexivity.
Qed.

Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof.
 reflexivity. Qed.

Record lazy_inv (L S : list (word * word)) (m : Model) : Prop := {
  li_lazy   : m_vm_lazy m = L;
  li_nodup  : List.NoDup (m_vm_materialized m);
  li_incl   : incl (m_vm_materialized m) (all_pages S);
  li_budget : (eager_used m + pages_total S * page_size <= vm_limit (m_vmmaps m))%Z
}.

Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 -> same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma same_but_materialized_fields : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m.
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] m' ->. cbn. repeat split; reflexivity.
Qed.

Lemma same_but_materialized_halted : forall m m',
  same_but_materialized m m' -> m_halted m' = m_halted m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_fs : forall m m',
  same_but_materialized m m' -> m_fs m' = m_fs m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_fds : forall m m',
  same_but_materialized m m' -> m_fds m' = m_fds m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

(* 75d69e00: writev's channel arm needs the far end's reader bit, and a
   materialisation step must not be able to lose it. *)
Lemma same_but_materialized_reader : forall m m',
  same_but_materialized m m' -> m_channel_reader m' = m_channel_reader m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_vmmaps : forall m m',
  same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_eager : forall m m',
  same_but_materialized m m' -> eager_used m' = eager_used m.
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] m' ->. reflexivity. Qed.

Lemma same_but_materialized_with_vm_backing : forall m pages,
  same_but_materialized m (with_vm_backing (m_vm_lazy m) pages m).
Proof.
 intros [fd [maps lazy mat] io fs proc lim tm] pages. reflexivity. Qed.

Lemma bv_unsigned_add_Z_to_bv : forall (a : word) z,
  bv_unsigned (a + Z_to_bv 64 z) = ((bv_unsigned a + z) mod 2 ^ 64)%Z.
Proof.
  intros a z. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z. apply Zplus_mod_idemp_r.
Qed.

Lemma page_base_of_unsigned : forall z,
  (0 <= z)%Z ->
  bv_unsigned (page_base_of z) = (((z mod 2 ^ 64) / page_size) * page_size)%Z.
Proof.
  intros z Hz. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64)%Z.
  set (M := (2 ^ 64)%Z). set (ps := page_size).
  assert (HM : M = (ps * 2 ^ 52)%Z) by reflexivity.
  assert (Hps : (0 < ps)%Z) by (unfold ps, page_size; lia).
  set (q := (z / M)%Z). set (r := (z mod M)%Z).
  assert (Hzqr : z = (M * q + r)%Z) by (unfold q, r; apply Z.div_mod; unfold M; lia).
  assert (Hr : (0 <= r < M)%Z) by (unfold r; apply Z.mod_pos_bound; unfold M; lia).
  assert (Hdiv : (z / ps = 2 ^ 52 * q + r / ps)%Z).
  { rewrite Hzqr, HM. replace (ps * 2 ^ 52 * q + r)%Z with ((2 ^ 52 * q) * ps + r)%Z by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite Hdiv.
  replace ((2 ^ 52 * q + r / ps) * ps)%Z with (r / ps * ps + q * M)%Z by flia.
  rewrite Z.mod_add by (unfold M; lia).
  apply Z.mod_small.
  pose proof (Z.mul_div_le r ps Hps) as H1.
  assert (0 <= r / ps)%Z by (apply Z.div_pos; lia).
  flia.
Qed.

Lemma page_of_access_byte : forall (a : word) (k : nat),
  let x := bv_unsigned (a + Z_to_bv 64 (Z.of_nat k)) in
  let p := bv_unsigned (page_base_of (bv_unsigned a + Z.of_nat k)) in
  p = ((x / page_size) * page_size)%Z /\ (p <= x < p + page_size)%Z.
Proof.
  intros a k. cbn zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  rewrite page_base_of_unsigned by lia.
  rewrite <- bv_unsigned_add_Z_to_bv.
  set (x := bv_unsigned (a + Z_to_bv 64 (Z.of_nat k))).
  pose proof (bv_unsigned_in_range 64 (a + Z_to_bv 64 (Z.of_nat k))) as Hx. fold x in Hx.
  split; [reflexivity|].
  pose proof (Z.div_mod x page_size ltac:(unfold page_size; lia)).
  pose proof (Z.mod_pos_bound x page_size ltac:(unfold page_size; lia)).
  unfold page_size in *. lia.
Qed.

Lemma window_page_in_all_pages : forall S (x : word) (p : word),
  in_rangesb x S = true ->
  bv_unsigned p = ((bv_unsigned x / page_size) * page_size)%Z ->
  In p (all_pages S).
Proof.
  induction S as [|r S IH]; intros x p Hin Hp.
  - cbn in Hin. discriminate.
  - cbn [all_pages]. apply in_app_iff.
    unfold in_rangesb in Hin. cbn [existsb] in Hin. apply orb_true_iff in Hin.
    destruct Hin as [Hin | Hin]; [left | right; apply (IH x p); [exact Hin | exact Hp]].
    clear IH.
    pose proof (cl_bounds r) as (C1 & C2 & C3 & C4 & C5 & C6).
    destruct r as [b n]. unfold zin_rangeb in Hin. cbn [fst snd] in Hin, C1, C2.
    unfold cl_lo, cl_hi, win_npagesZ in *. cbn [fst snd] in *.
    apply andb_true_iff in Hin. destruct Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    pose proof (bv_unsigned_in_range 64 x) as Hx.
    set (ux := bv_unsigned x) in *. set (lo := bv_unsigned b) in *. set (sz := bv_unsigned n) in *.
    assert (Hlo : (lo / page_size <= ux / page_size)%Z) by (apply Z.div_le_mono; unfold page_size; lia).
    assert (Hhi : (ux / page_size + 1 <= (lo + sz + page_size - 1) / page_size)%Z).
    { replace (ux / page_size + 1)%Z with ((ux + 1 * page_size) / page_size)%Z
        by (rewrite Z.div_add by (unfold page_size; lia); reflexivity).
      apply Z.div_le_mono; unfold page_size; lia. }
    unfold win_pages. apply in_map_iff. exists (Z.to_nat (ux / page_size - lo / page_size))%Z. split.
    + unfold win_page, cl_lo. cbn [fst]. apply bv_eq. rewrite Z_to_bv_unsigned.
      rewrite Z2Nat.id by lia. fold lo.
      replace (lo / page_size * page_size + page_size * (ux / page_size - lo / page_size))%Z
        with (ux / page_size * page_size)%Z by lia.
      rewrite <- Hp. apply bv_wrap_small. apply bv_unsigned_in_range.
    + apply in_seq. unfold win_npages, win_npagesZ, cl_lo, cl_hi. cbn [fst snd]. fold lo sz.
      replace ((lo + sz + page_size - 1) / page_size * page_size - lo / page_size * page_size)%Z
        with (((lo + sz + page_size - 1) / page_size - lo / page_size) * page_size)%Z by lia.
      rewrite Z.div_mul by (unfold page_size; lia).
      clear - Hlo Hhi. generalize dependent (ux / page_size)%Z. generalize dependent (lo / page_size)%Z.
      generalize dependent ((lo + sz + page_size - 1) / page_size)%Z. intros q1 q2 q3 Hlo Hhi. lia.
Qed.

Lemma page_in_ranges_addr : forall L (p x : word),
  page_in_ranges p L = true ->
  (bv_unsigned p <= bv_unsigned x < bv_unsigned p + page_size)%Z ->
  in_rangesb x L = true.
Proof.
  intros L p x Hp Hx. unfold page_in_ranges in Hp. apply existsb_exists in Hp.
  destruct Hp as ([lo sz] & Hin & Ht). cbn [fst snd] in Ht.
  apply andb_true_iff in Ht. destruct Ht as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply in_rangesb_true. exists lo, sz. split; [exact Hin | lia].
Qed.

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hin & He). unfold bv_eqb in He. apply Z.eqb_eq in He. apply bv_eq in He. subst; exact Hin.
  - intros Hin. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

Lemma NoDup_page_insert : forall q pages, List.NoDup pages -> List.NoDup (page_insert q pages).
Proof.
  intros q pages H. unfold page_insert. destruct (page_mem q pages) eqn:E; [exact H|].
  constructor; [|exact H]. intros Hin. apply page_mem_In in Hin. congruence.
Qed.

Lemma NoDup_access_pages_acc : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages H; [exact H|].
  apply IH. apply NoDup_page_insert. exact H.
Qed.

Lemma NoDup_accesses_pages : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages H; [exact H|].
  apply IH. apply NoDup_access_pages_acc. exact H.
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.

Lemma newly_materialized_pages_visible : forall L S mat rs,
  ranges_visible (hiddenb L S) rs ->
  let new := newly_materialized_pages L mat rs in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ incl new (all_pages S).
Proof.
  intros L S mat rs Hvis. cbn zeta.
  unfold newly_materialized_pages. split; [|split].
  - apply NoDup_filter. apply NoDup_accesses_pages. constructor.
  - intros p Hp Hin. apply filter_In in Hp. destruct Hp as [_ Hp].
    apply andb_true_iff in Hp. destruct Hp as [_ Hm].
    apply page_mem_In in Hin. rewrite Hin in Hm. discriminate.
  - intros p Hp. apply filter_In in Hp. destruct Hp as [Hacc Hp].
    apply andb_true_iff in Hp. destruct Hp as [HpL _].
    destruct (accesses_pages_in rs [] p Hacc) as [[] | (a & n & k & Hin & Hk & ->)].
    pose proof (Hvis a n Hin k Hk) as Hhid.
    destruct (page_of_access_byte a k) as [Hpx Hbr].
    set (x := a + Z_to_bv 64 (Z.of_nat k)) in *.
    unfold hiddenb in Hhid.
    destruct (in_rangesb x S) eqn:ES.
    + exact (window_page_in_all_pages S x _ ES Hpx).
    + rewrite (page_in_ranges_addr L _ x HpL Hbr) in Hhid. discriminate.
Qed.

Theorem materialize_restrict : forall L S m rs,
  lazy_inv L S m ->
  ranges_visible (hiddenb L S) rs ->
  exists pages,
    materialize_model_accesses m rs = Some (with_vm_backing (m_vm_lazy m) pages m)
    /\ lazy_inv L S (with_vm_backing (m_vm_lazy m) pages m).
Proof.
  intros L S m rs Hinv Hvis.
  destruct Hinv as [Hlazy Hnd Hincl Hbud].
  pose proof (newly_materialized_pages_visible L S (m_vm_materialized m) rs Hvis) as Hnew.
  cbn zeta in Hnew. destruct Hnew as (Hnnd & Hfresh & Hnincl).
  set (new := newly_materialized_pages L (m_vm_materialized m) rs) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m))
    by (apply NoDup_app; assumption).
  assert (Happ_incl : incl (new ++ m_vm_materialized m) (all_pages S))
    by (apply incl_app; assumption).
  assert (Hlen : (Z.of_nat (length (new ++ m_vm_materialized m)) <= pages_total S)%Z).
  { rewrite <- all_pages_length. apply Nat2Z.inj_le. apply NoDup_incl_length; assumption. }
  assert (Hgoal : forall pages,
            (pages = m_vm_materialized m \/ pages = new ++ m_vm_materialized m) ->
            lazy_inv L S (with_vm_backing (m_vm_lazy m) pages m)).
  { intros pages Hp.
    destruct m as [fd [maps lazy mat] io fs proc lim tm]. cbn in *. subst lazy.
    split; cbn.
    - reflexivity.
    - destruct Hp as [-> | ->]; assumption.
    - destruct Hp as [-> | ->]; assumption.
    - exact Hbud. }
  unfold materialize_model_accesses, materialize_accesses.
  replace (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) rs) with new
    by (unfold new; rewrite Hlazy; reflexivity).
  destruct new as [|p new'] eqn:En.
  - exists (m_vm_materialized m). split; [reflexivity|]. apply Hgoal. left; reflexivity.
  - rewrite vm_backing_used_split.
    rewrite length_app, Nat2Z.inj_add in Hlen.
    match goal with |- context [if ?c then _ else _] => replace c with true end.
    + exists ((p :: new') ++ m_vm_materialized m). split; [reflexivity|].
      apply Hgoal. right; reflexivity.
    + symmetry. apply Z.leb_le. clear - Hlen Hbud. unfold page_size in *. nia.
Qed.

Section HiddenInv.
Variables L S : list (word * word).

Definition hidden_inv (P : option byte -> Prop) (msF : machine_state) : Prop :=
  forall a, hiddenb L S a = true -> P (ms_mem msF a).

Definition hidden_const : machine_state -> Prop :=
  hidden_inv (fun o => exists b, o = Some b).

Definition hidden_zero : machine_state -> Prop :=
  hidden_inv (fun o => o = Some (Z_to_bv 8 0)).

Lemma unrestrict_restrict_self : forall msF,
  unrestrict_to L S msF (restrict L S msF) = msF.
Proof.
  intros [regs fregs pc svc resv fcsr m rom].
  unfold unrestrict_to, restrict, unrestrict_by, restrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros x.
  unfold unrestrict_mem_by, restrict_mem_by. destruct (hiddenb L S x); reflexivity.
Qed.

End HiddenInv.

Section Windows.
Variable L : list (word * word).

Lemma lazy_inv_windows_mono : forall S S' m,
  lazy_inv L S m ->
  incl (all_pages S) (all_pages S') ->
  (eager_used m + pages_total S' * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L S' m.
Proof.
  intros S S' m [Hl Hnd Hincl Hb] Hsub Hb'. split; try assumption.
  eapply incl_tran; eassumption.
Qed.

Lemma pages_total_cons : forall W S,
  pages_total (W :: S) = (win_npagesZ W + pages_total S)%Z.
Proof.
 reflexivity. Qed.

Lemma pages_total_app : forall S1 S2,
  pages_total (S1 ++ S2) = (pages_total S1 + pages_total S2)%Z.
Proof.
 induction S1 as [|r S1 IH]; intros S2; cbn [pages_total app]; [lia | rewrite IH; lia]. Qed.

Lemma lazy_inv_open_window : forall W S m,
  lazy_inv L S m ->
  (eager_used m + pages_total (W :: S) * page_size <= vm_limit (m_vmmaps m))%Z ->
  lazy_inv L (W :: S) m.
Proof.
  intros W S m Hinv Hb. eapply lazy_inv_windows_mono; [exact Hinv | | exact Hb].
  cbn [all_pages]. apply incl_appr. apply incl_refl.
Qed.

Lemma in_rangesb_cons : forall a W S,
  in_rangesb a (W :: S) = zin_rangeb (bv_unsigned a) W || in_rangesb a S.
Proof.
 reflexivity. Qed.

Lemma in_rangesb_app : forall a S1 S2,
  in_rangesb a (S1 ++ S2) = in_rangesb a S1 || in_rangesb a S2.
Proof.
 intros a S1 S2. unfold in_rangesb. apply existsb_app. Qed.

Lemma hiddenb_cons_window : forall W S a,
  hiddenb L (W :: S) a = hiddenb L S a && negb (zin_rangeb (bv_unsigned a) W).
Proof.
  intros W S a. unfold hiddenb. rewrite in_rangesb_cons.
  destruct (in_rangesb a L), (zin_rangeb (bv_unsigned a) W), (in_rangesb a S); reflexivity.
Qed.

Lemma hiddenb_mono_cons : forall W S a,
  hiddenb L (W :: S) a = true -> hiddenb L S a = true.
Proof.
  intros W S a H. rewrite hiddenb_cons_window in H. apply andb_true_iff in H. tauto.
Qed.

Lemma restrict_mem_open_window : forall W S m a,
  restrict_mem L (W :: S) m a
  = if zin_rangeb (bv_unsigned a) W then m a else restrict_mem L S m a.
Proof.
  intros W S m a. unfold restrict_mem, restrict_mem_by. rewrite hiddenb_cons_window.
  destruct (zin_rangeb (bv_unsigned a) W), (hiddenb L S a); reflexivity.
Qed.

Lemma restrict_open_window_eq : forall W S msF,
  restrict L (W :: S) msF
  = with_mem (restrict L S msF)
      (fun a => if zin_rangeb (bv_unsigned a) W then ms_mem msF a
                else ms_mem (restrict L S msF) a).
Proof.
  intros W S msF. unfold restrict, restrict_by, with_mem. cbn. f_equal.
  apply functional_extensionality. intros a. apply restrict_mem_open_window.
Qed.

Lemma lazy_inv_vm_frame : forall S m m',
  m_vm m' = m_vm m -> lazy_inv L S m -> lazy_inv L S m'.
Proof.
  intros S [fd vm io fs proc lim tm] [fd' vm' io' fs' proc' lim' tm'] E H.
  cbn in E. subst vm'. destruct H as [Hl Hnd Hincl Hb]. split; assumption.
Qed.

End Windows.

Section LazyLedger.

Lemma hiddenb_cons_lazy : forall r L S a,
  hiddenb (r :: L) S a
  = (zin_rangeb (bv_unsigned a) r && negb (in_rangesb a S)) || hiddenb L S a.
Proof.
  intros r L S a. unfold hiddenb. rewrite in_rangesb_cons.
  destruct (zin_rangeb (bv_unsigned a) r), (in_rangesb a L), (in_rangesb a S); reflexivity.
Qed.

Lemma m_vm_lazy_vm_add_lazy : forall a n m,
  m_vm_lazy (vm_add_lazy a n m) = lazy_interior a n ++ m_vm_lazy m.
Proof.
 intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_materialized_vm_add_lazy : forall a n m,
  m_vm_materialized (vm_add_lazy a n m) = m_vm_materialized m.
Proof.
 intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vmmaps_vm_add_lazy : forall a n m,
  m_vmmaps (vm_add_lazy a n m) = m_vmmaps m.
Proof.
 intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_lazy_vm_forget_range : forall lo hi m,
  m_vm_lazy (vm_forget_range lo hi m) = maps_subtract (m_vm_lazy m) lo hi.
Proof.
 intros lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_materialized_vm_forget_range : forall lo hi m,
  m_vm_materialized (vm_forget_range lo hi m)
  = List.filter (page_outside_range lo hi) (m_vm_materialized m).
Proof.
 intros lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m,
  m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof.
 intros lo hi [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_lazy_with_vmmaps : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof.
 intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vm_materialized_with_vmmaps : forall h m,
  m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof.
 intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma m_vmmaps_with_vmmaps : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof.
 intros h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma lazy_interior_aligned : forall a n,
  (bv_unsigned a mod page_size = 0)%Z ->
  (bv_unsigned n mod page_size = 0)%Z ->
  (0 < bv_unsigned n)%Z ->
  lazy_interior a n = [(a, n)].
Proof.
  intros a n Ha Hn Hpos. unfold lazy_interior.
  pose proof (bv_unsigned_in_range 64 a) as Har. pose proof (bv_unsigned_in_range 64 n) as Hnr.
  set (lo := bv_unsigned a) in *. set (sz := bv_unsigned n) in *.
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  pose proof (Z.div_mod lo page_size ltac:(lia)) as Hlo.
  pose proof (Z.div_mod (lo + sz) page_size ltac:(lia)) as Hhi.
  pose proof (Z.div_mod (lo + page_size - 1) page_size ltac:(lia)) as Hlo'.
  pose proof (Z.mod_pos_bound (lo + page_size - 1) page_size ltac:(lia)) as Hm'.
  assert (Hsum : ((lo + sz) mod page_size = 0)%Z).
  { rewrite Z.add_mod, Ha, Hn by lia. reflexivity. }
  assert (E1 : ((lo + page_size - 1) / page_size * page_size = lo)%Z).
  { replace (lo + page_size - 1)%Z with (lo / page_size * page_size + (page_size - 1))%Z in * by lia.
    rewrite Z.div_add_l in * by lia.
    rewrite (Z.div_small (page_size - 1) page_size) by lia. lia. }
  assert (E2 : ((lo + sz) / page_size * page_size = lo + sz)%Z) by lia.
  rewrite E1, E2.
  destruct (lo <? lo + sz)%Z eqn:E; [|apply Z.ltb_ge in E; lia].
  f_equal. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Har.
  - apply bv_eq. rewrite Z_to_bv_unsigned. replace (lo + sz - lo)%Z with sz by lia.
    apply bv_wrap_small. exact Hnr.
Qed.

Lemma iv_subtract_within : forall a sz lo hi b m,
  (bv_unsigned a + bv_unsigned sz <= 2 ^ 64)%Z ->
  (hi <= 2 ^ 64)%Z ->
  In (b, m) (iv_subtract a sz lo hi) ->
  (bv_unsigned a <= bv_unsigned b)%Z
  /\ (bv_unsigned b + bv_unsigned m <= bv_unsigned a + bv_unsigned sz)%Z.
Proof.
  intros a sz lo hi b m Hnw Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a) as Har. pose proof (bv_unsigned_in_range 64 sz) as Hszr.
  change (bv_modulus 64) with (2^64)%Z in Har, Hszr.
  apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo)%Z eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [Hin|[]]. inversion Hin; subst.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz)%Z eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
    destruct Hin as [Hin|[]]. inversion Hin; subst.
    pose proof (Z.le_max_l (bv_unsigned a) hi). pose proof (Z.le_max_r (bv_unsigned a) hi).
    assert (Z.max (bv_unsigned a) hi < 2 ^ 64)%Z by lia.
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia). lia.
Qed.

Lemma lazy_range_okb_within : forall segs a sz b m,
  lazy_range_okb segs (a, sz) = true ->
  (bv_unsigned a <= bv_unsigned b)%Z ->
  (bv_unsigned b + bv_unsigned m <= bv_unsigned a + bv_unsigned sz)%Z ->
  lazy_range_okb segs (b, m) = true.
Proof.
  intros segs a sz b m H Hlo Hhi. unfold lazy_range_okb, range_nowrapb in *. cbn [fst snd] in *.
  apply andb_true_iff in H. destruct H as [Hnw Hd]. apply Z.leb_le in Hnw.
  apply andb_true_iff. split; [apply Z.leb_le; lia|].
  rewrite forallb_forall in Hd |- *. intros seg Hin. specialize (Hd seg Hin).
  unfold seg_disjoint_rangeb in *. cbn [fst snd] in *.
  rewrite orb_true_iff in Hd |- *. rewrite !Z.leb_le in Hd |- *. lia.
Qed.

Lemma lazy_ranges_okb_maps_subtract : forall segs L lo hi,
  (hi <= 2 ^ 64)%Z ->
  lazy_ranges_okb segs L = true ->
  lazy_ranges_okb segs (maps_subtract L lo hi) = true.
Proof.
  intros segs L lo hi Hhi H. induction L as [|[a sz] L IH].
  - cbn [maps_subtract]. rewrite lazy_ranges_okb_nil.
    unfold lazy_ranges_okb in H. apply andb_true_iff in H. tauto.
  - apply lazy_ranges_okb_cons in H. destruct H as [Hr HL].
    cbn [maps_subtract]. apply lazy_ranges_okb_app. split; [|exact (IH HL)].
    unfold lazy_ranges_okb. apply andb_true_iff. split.
    + unfold lazy_ranges_okb in HL. apply andb_true_iff in HL. tauto.
    + apply forallb_forall. intros [b m] Hin.
      assert (Hnw : (bv_unsigned a + bv_unsigned sz <= 2 ^ 64)%Z).
      { unfold lazy_range_okb, range_nowrapb in Hr. cbn [fst snd] in Hr.
        apply andb_true_iff in Hr. destruct Hr as [Hr _]. apply Z.leb_le in Hr. exact Hr. }
      destruct (iv_subtract_within a sz lo hi b m Hnw Hhi Hin) as [H1 H2].
      exact (lazy_range_okb_within segs a sz b m Hr H1 H2).
Qed.

End LazyLedger.

Section Clients.
Variables L S : list (word * word).

End Clients.
