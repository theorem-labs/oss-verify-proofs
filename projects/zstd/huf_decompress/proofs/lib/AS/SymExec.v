(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (57 recorded proofs replaced by written proofs (Z_to_bv64_wrap_l, Z_to_bv64_wrap_r, Z_to_bv64_wrap_sub and 54 more)). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk Footprint.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_SymExec () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp7tactics<f_equal_helpC47Corelib7Classes9MorphismsGrewrite_relation_eq_domC47Corelib4Init5Logic8eq_ind_rC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib2AS8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive03C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01C46Stdlib6ZArith4ZdivBZminus_mod_idemp_rC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lc59OSSVerify5KrLib2AS7SymExec@Z_to_bv64_wrap_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec:v_addi_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec@Z_to_bv64_wrap_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7v_auipcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib2AS8PropExec8jalr_tgtC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2ex01C46Stdlib6ZArith:Znumtheory<Zmod_div_modC59OSSVerify5KrLib2AS8PropExec=bv_wrap32_modC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp9bitvector;definitions:bv_extractC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z6shiftrc59OSSVerify5KrLib2AS7SymExec=bv_wrap_32_64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z:shiftr_0_rC45stdpp9bitvector;definitionsCbv_extract_unsignedC4ELinuxProcessSemantics5Riscv3Sem5low32K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics5Riscv7Prelude4sextc59OSSVerify5KrLib2AS7SymExec9low32_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4zextC59OSSVerify5KrLib2AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib2AS8PropExec7alu_addC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C59OSSVerify5KrLib2AS8PropExec5v_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExecBZ_to_bv64_wrap_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7alu_subC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib2AS7SymExecDZ_to_bv64_wrap_sub_rC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib2AS7SymExec9v_add_litC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib2AS7SymExecDZ_to_bv64_wrap_sub_lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec9v_sub_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec5mkAluC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec6edenotC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec4expr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec=alu64_add_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symk59OSSVerify5KrLib2AS7SymExec4expr02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec4expr03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExecAalu64_add_add_litC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec4expr04C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec4expr05C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec4expr06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec=alu64_sub_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExecAalu64_add_sub_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec3envC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00i59OSSVerify5KrLib2AS7SymExec4expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics5Riscv5Instr5mulop00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c59OSSVerify5KrLib2AS7SymExec4ridxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8u5_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib2AS7SymExec6sr_updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib2AS7SymExec9sbase_eqbC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec5sbase02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC56Stdlib5Arith8PeanoNat3Nat6eqb_eqK47Corelib4Init5Logic4True01i59OSSVerify5KrLib2AS7SymExec5sbase00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec5sbase01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib2AS7SymExec5a_offC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalk59OSSVerify5KrLib2AS7SymExec5saddr01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec6a_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec:v_add_commC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec6adenotC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib2AS7SymExec8to_saddrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec6bdenotC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib2AS7SymExec5saddr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec=u_Z_to_bv64_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec6sentry01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indi59OSSVerify5KrLib2AS7SymExec6sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec7regs_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics5Riscv3Sem7reg_getc59OSSVerify5KrLib2AS7SymExec8ridx_injC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8eqb_reflc59OSSVerify5KrLib2AS7SymExec6sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec:nth_sr_updC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K46Stdlib9micromega5Tauto4kind02C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC45stdpp9bitvector;definitionsCbv_wrap_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idc59OSSVerify5KrLib2AS7SymExec2E0C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc59OSSVerify5KrLib2AS7SymExec>ridx_roundtripC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec:ridx_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc59OSSVerify5KrLib2AS7SymExec5sr_idC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib2AS7SymExec5EplusC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3subc59OSSVerify5KrLib2AS7SymExec7sc_flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib2AS9Footprint5rg_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Footprint5rg_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Footprint5rg_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00K47Corelib4Init5Logic3and01C56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib2AS9Footprint6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Footprint7rg_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Footprint6coversC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Footprint=covers_nowrapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9Footprint;covers_disjC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec8sidecond03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec8sc_denotC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib2AS8PropExec4v_lwC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitions=bv_swrap_wrapC45stdpp9bitvector;definitions>bv_sign_extendC45stdpp9bitvector;definitionsGbv_sign_extend_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr06K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv3Sem5is_x0C45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib2AS8PropExec7fp_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6fp_csrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C59OSSVerify5KrLib2AS8PropExec=bv_eqb0_is_x0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6b_npc4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec8b_lw_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9le_word_vC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6ov_rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions?bv_add_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu32c59OSSVerify5KrLib2AS7SymExec;alu32_add_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec8mkSext32C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z7lor_0_rC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z:shiftl_0_lC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z;shiftr_specC56Stdlib6ZArith6BinInt1ZAmod_pow2_bits_lowC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1ZBmod_pow2_bits_highC56Stdlib6ZArith6BinInt1Z9bits_inj'C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib2AS7SymExec<mod_pow2_lowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec@shiftr8_mod_pow2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib2AS7SymExecAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memc59OSSVerify5KrLib2AS7SymExec>low32_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExecCwrite_to_mem_wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec9scs_denotC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00i59OSSVerify5KrLib2AS7SymExec8sidecond00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec8log_flatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec6flat_uC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbc59OSSVerify5KrLib2AS7SymExec9sm_lookupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec<sbase_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib2AS7SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib2AS7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec@rdn_wbytes_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExecCrdn_wbytes_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec>scs_denot_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec5st_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec4s_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec5s_logC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01c59OSSVerify5KrLib2AS7SymExec6s_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec6s_nextC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec9sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec5v_luiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec4ssetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_luiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec;regs_ok_updC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr02C59OSSVerify5KrLib2AS8PropExec:step_auipcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec;v_auipc_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec8btgt_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04C59OSSVerify5KrLib2AS7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec9step_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9jalr_tgtZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec<jalr_tgt_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05c59OSSVerify5KrLib2AS7SymExec;msize_bytesC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec8sidecond02C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismc59OSSVerify5KrLib2AS7SymExec>to_saddr_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec?sm_lookup_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7step_ldC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec8sidecond05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec?bytes_le_to_Z_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_lbuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib2AS8PropExec8step_lhuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec7step_lwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec>mkSext32_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_lwuC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib2AS7SymExec8sidecond04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec?mem_denot_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec7step_sbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec;step_sw_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec;step_sd_valC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08C59OSSVerify5KrLib2AS8PropExec>step_opimm_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec:sext64_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec;mkAlu_denotC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09C59OSSVerify5KrLib2AS8PropExecAstep_shiftimm_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec:zext64_litC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:C59OSSVerify5KrLib2AS8PropExec;step_op_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;C59OSSVerify5KrLib2AS8PropExec@step_opimm32_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec<sext32_low32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0<C59OSSVerify5KrLib2AS8PropExecCstep_shiftimm32_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec<zext32_low32C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=C59OSSVerify5KrLib2AS8PropExec=step_op32_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?K4ELinuxProcessSemantics5Riscv5Instr5instr0BC4ELinuxProcessSemantics5Riscv3Sem7mul_divC59OSSVerify5KrLib2AS8PropExec<step_mul_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0CC59OSSVerify5KrLib2AS8PropExec>step_mul32_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JK4ELinuxProcessSemantics5Riscv5Instr5instr0KK4ELinuxProcessSemantics5Riscv5Instr5instr0LK4ELinuxProcessSemantics5Riscv5Instr5instr0MK4ELinuxProcessSemantics5Riscv5Instr5instr0NK4ELinuxProcessSemantics5Riscv5Instr5instr0OK4ELinuxProcessSemantics5Riscv5Instr5instr0PK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0Sc59OSSVerify5KrLib2AS7SymExec8sym_stepC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00i59OSSVerify5KrLib2AS7SymExec9sym_state00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01K4ELinuxProcessSemantics5Riscv5Instr5msize02K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv5Instr4ffmt00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00C47Corelib4Init9Datatypes4negbc59OSSVerify5KrLib2AS7SymExec8sym_execC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec5sjumpC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init9Datatypes3sndk59OSSVerify5KrLib2AS7SymExec8sidecond01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List9in_or_appI46Stdlib5Lists4List6Exists00I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec<sym_exec_accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec=scs_denot_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS7SymExec>sym_step_soundC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms<PER_morphismC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC4ELinuxProcessSemantics5Riscv3Sem<branch_takenC47Corelib7Classes9MorphismsBsubrelation_properC59OSSVerify5KrLib2AS8PropExecBstep_branch_tk_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExecBstep_branch_ft_genC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC47Corelib7Program6Basics4implc59OSSVerify5KrLib2AS7SymExec>sym_exec_soundC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive expr : Type :=
| ELit  (z : Z)
| EVar  (n : nat)
| EAlu  (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)   (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)   (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr).  (* [comment removed for export] *)

Definition env := nat -> word.

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv64_wrap_l : forall a b, Z_to_bv 64 (bv_wrap 64 a + b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_l.
Qed.

Lemma Z_to_bv64_wrap_r : forall a b, Z_to_bv 64 (a + bv_wrap 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

Lemma Z_to_bv64_wrap_sub : forall a b,
  Z_to_bv 64 (bv_wrap 64 a - bv_wrap 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_l. Qed.

Lemma btgt_lit : forall p i, btgt (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros. apply v_addi_lit. Qed.

Lemma v_auipc_lit : forall p i, v_auipc (Z_to_bv 64 p) i = Z_to_bv 64 (i + p).
Proof.
  intros p i. unfold v_auipc. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.

Lemma jalr_tgt_lit : forall z i,
  jalr_tgt (Z_to_bv 64 z) i = Z_to_bv 64 (Z.land (bv_wrap 64 z + i) (-2)).
Proof. intros z i. unfold jalr_tgt, jalr_tgtZ. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. reflexivity. Qed.

Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_wrap_32_64 : forall z, bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z.
Proof.
  intro z. rewrite bv_wrap32_mod, !bv_wrap64_mod, bv_wrap32_mod.
  rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia |].
  exists (2^32)%Z. reflexivity.
Qed.

Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
  intro z. unfold low32. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
  apply bv_wrap_32_64.
Qed.

Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkAlu (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x + y)
          | EAlu ALU_ADD a' (ELit x) => EAlu ALU_ADD a' (ELit (x + y))
          | _ => EAlu ALU_ADD a b
          end
      | _ => EAlu ALU_ADD a b
      end
  | ALU_SUB =>
      match b with
      | ELit y =>
          match a with
          | ELit x => ELit (x - y)
          | EAlu ALU_ADD a' (ELit x) => EAlu ALU_ADD a' (ELit (x - y))
          | _ => EAlu ALU_SUB a b
          end
      | _ => EAlu ALU_SUB a b
      end
  | _ => EAlu op a b
  end.

Lemma alu64_add_lit : forall x y,
  alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. rewrite alu_add. unfold v_add. rewrite !Z_to_bv_unsigned.
  rewrite Z_to_bv64_wrap_l, Z_to_bv64_wrap_r. reflexivity.
Qed.

Lemma alu64_sub_lit : forall x y,
  alu64 ALU_SUB (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
  intros x y. rewrite alu_sub. unfold v_sub. rewrite !Z_to_bv_unsigned.
  apply Z_to_bv64_wrap_sub.
Qed.

(* [comment removed for export] *)
Lemma Z_to_bv64_wrap_sub_l : forall a b,
  Z_to_bv 64 (bv_wrap 64 a - b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_l.
Qed.

Lemma Z_to_bv64_wrap_sub_r : forall a b,
  Z_to_bv 64 (a - bv_wrap 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

(* [comment removed for export] *)
Lemma v_add_lit : forall (u : word) x,
  v_add u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u + x).
Proof.
  intros u x. unfold v_add. rewrite Z_to_bv_unsigned. apply Z_to_bv64_wrap_r.
Qed.

Lemma v_add_comm : forall x y : word, v_add x y = v_add y x.
Proof. intros x y. unfold v_add. f_equal. lia. Qed.

Lemma v_sub_lit : forall (u : word) x,
  v_sub u (Z_to_bv 64 x) = Z_to_bv 64 (bv_unsigned u - x).
Proof.
  intros u x. unfold v_sub. rewrite Z_to_bv_unsigned.
  apply Z_to_bv64_wrap_sub_r.
Qed.

Lemma alu64_add_add_lit : forall (u : word) x y,
  alu64 ALU_ADD (alu64 ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
  = alu64 ALU_ADD u (Z_to_bv 64 (x + y)).
Proof.
  intros u x y. rewrite !alu_add, !v_add_lit, Z_to_bv_unsigned,
    Z_to_bv64_wrap_l. f_equal. lia.
Qed.

Lemma alu64_add_sub_lit : forall (u : word) x y,
  alu64 ALU_SUB (alu64 ALU_ADD u (Z_to_bv 64 x)) (Z_to_bv 64 y)
  = alu64 ALU_ADD u (Z_to_bv 64 (x - y)).
Proof.
  intros u x y. rewrite alu_sub, !alu_add, !v_add_lit, !v_sub_lit,
    !Z_to_bv_unsigned, !Z_to_bv64_wrap_sub_l. f_equal. lia.
Qed.

Lemma mkAlu_denot : forall E op a b,
  edenot E (mkAlu op a b) = alu64 op (edenot E a) (edenot E b).
Proof.
  intros E op a b. destruct op; try reflexivity;
    (destruct b as [y| | | | | ]; [|reflexivity..]);
    (destruct a as [x| |op' a1 a2| | | ]; [| |  |reflexivity..]);
    try reflexivity;
    try (cbn [edenot]; auto using alu64_add_lit, alu64_sub_lit; fail);
    destruct op'; try reflexivity;
    (destruct a2 as [z| | | | | ]; [|reflexivity..]);
    cbn [edenot]; auto using alu64_add_add_lit, alu64_add_sub_lit.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof.
  intros r r' H. apply bv_eq. unfold ridx in H.
  pose proof (u5_range r). pose proof (u5_range r').
  lia.
Qed.

(* [comment removed for export] *)
Definition sr_get (sr : list expr) (r : reg) : expr :=
  if bv_eqb r 0 then ELit 0 else nth (ridx r) sr (ELit 0).

(* [comment removed for export] *)
Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Lemma nth_sr_upd : forall n sr e i,
  nth i (sr_upd sr n e) (ELit 0) =
    if Nat.eqb i n then e else nth i sr (ELit 0).
Proof.
  induction n as [|n IH]; intros sr e i.
  - destruct sr; destruct i; cbn; try reflexivity;
      destruct i; reflexivity.
  - destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
    + rewrite IH. destruct (Nat.eqb i n); [reflexivity|].
      destruct i; reflexivity.
    + apply IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sbase : Type :=
| SBLit
| SBVar (n : nat).

Definition sbase_eqb (b1 b2 : sbase) : bool :=
  match b1, b2 with
  | SBLit, SBLit => true
  | SBVar n, SBVar m => Nat.eqb n m
  | _, _ => false
  end.

Lemma sbase_eqb_eq : forall b1 b2, sbase_eqb b1 b2 = true -> b1 = b2.
Proof.
  intros [|n] [|m] H; try discriminate; [reflexivity|].
  cbn in H. apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

Record saddr : Type := SA { a_base : sbase; a_off : Z }.

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

Definition bdenot (E : env) (b : sbase) : word :=
  match b with SBLit => Z_to_bv 64 0 | SBVar n => E n end.

(* [comment removed for export] *)
Definition adenot (E : env) (a : saddr) : word :=
  v_addi (bdenot E (a_base a)) (a_off a).

(* [comment removed for export] *)
Definition to_saddr (e : expr) (i : Z) : option saddr :=
  match e with
  | ELit z => Some (SA SBLit (z + i))
  | EVar n => Some (SA (SBVar n) i)
  | EAlu ALU_ADD (EVar n) (ELit z) => Some (SA (SBVar n) (z + i))
  | EAlu ALU_ADD (ELit z) (EVar n) => Some (SA (SBVar n) (z + i))
  | _ => None
  end.

Lemma u_Z_to_bv64_0 : bv_unsigned (Z_to_bv 64 0) = 0%Z.
Proof. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma to_saddr_denot : forall E e i a,
  to_saddr e i = Some a -> adenot E a = v_addi (edenot E e) i.
Proof.
  intros E e i a H. unfold adenot.
  destruct e as [z|n|op e1 e2| | | ]; cbn in H;
    try discriminate.
  - injection H as <-. cbn [a_base a_off bdenot edenot].
    unfold v_addi. rewrite u_Z_to_bv64_0, Z_to_bv_unsigned,
      Z_to_bv64_wrap_l. f_equal; lia.
  - injection H as <-. reflexivity.
  - destruct op; cbn in H; try discriminate.
    destruct e1; destruct e2; cbn in H; try discriminate;
      injection H as <-; cbn [a_base a_off bdenot edenot]; rewrite alu_add.
    + (* [comment removed for export] *)
      rewrite v_add_comm, v_add_lit. unfold v_addi.
      rewrite Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal; lia.
    + (* [comment removed for export] *)
      rewrite v_add_lit. unfold v_addi.
      rewrite Z_to_bv_unsigned, Z_to_bv64_wrap_l. f_equal; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sym_state : Type := SS {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;
  s_next : nat
}.

(* [comment removed for export] *)
Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_next ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition regs_ok (E : env) (sr : list expr) (regs : bvmap 5 word) : Prop :=
  forall r : reg, getr regs r = edenot E (sr_get sr r).

(* [comment removed for export] *)
Fixpoint mem_denot (E : env) (base : word -> option byte)
                   (log : list sentry) : word -> option byte :=
  match log with
  | [] => base
  | SE a w v :: rest =>
      wbytes (mem_denot E base rest) (adenot E a)
             (word_to_le_bytes w (edenot E v))
  end.

(* [comment removed for export] *)
Lemma mem_denot_grows : forall E base log, mem_grows base (mem_denot E base log).
Proof.
  intros E base log. induction log as [|[a w v] rest IH]; cbn [mem_denot].
  - apply mem_grows_refl.
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

(* [comment removed for export] *)
Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE a w _ :: rest =>
      (0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
      /\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
      /\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat w <= 2^64)%Z
      /\ log_flat E rest
  end.

(* [comment removed for export] *)
Definition st_ok (E : env) (base rom : word -> option byte)
                 (ss : sym_state) (ms : machine_state) : Prop :=
  exists regs, ms = mkst regs (Z_to_bv 64 (s_pc ss))
                          (mem_denot E base (s_log ss)) rom
            /\ regs_ok E (s_regs ss) regs
            /\ log_flat E (s_log ss).

Lemma regs_ok_upd : forall E sr regs rd v e,
  regs_ok E sr regs ->
  edenot E e = v ->
  regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
            (if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
  intros E sr regs rd v e Hr Hv.
  destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
  assert (Hne : rd <> 0).
  { intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
  intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd.
    destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
      rewrite getr_same by exact Hne. exact (eq_sym Hv).
    + assert (Hrr : r <> rd).
      { intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
      rewrite getr_other by exact Hrr.
      specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma regs_ok_pin : forall E sr regs (r : reg) e,
  regs_ok E sr regs ->
  getr regs r = edenot E e ->
  regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
  intros E sr regs r e Hr Hv r'. unfold sr_get.
  destruct (bv_eqb r' 0) eqn:Hr0.
  - assert (r' = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r'. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact Hv.
    + specialize (Hr r'). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Definition sr_id : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7;
   EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Definition E0 (regs : bvmap 5 word) : env :=
  fun n => getr regs (Z_to_bv 5 (Z.of_nat n)).

Lemma ridx_range : forall r : reg, (ridx r < 32)%nat.
Proof. intro r. unfold ridx. pose proof (u5_range r). lia. Qed.

Lemma ridx_roundtrip : forall r : reg, Z_to_bv 5 (Z.of_nat (ridx r)) = r.
Proof.
  intro r. apply bv_eq. unfold ridx. rewrite Z_to_bv_unsigned.
  pose proof (u5_range r). rewrite Z2Nat.id by lia.
  apply bv_wrap_bv_unsigned.
Qed.

Lemma regs_ok_id : forall regs, regs_ok (E0 regs) sr_id regs.
Proof.
  intros regs r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - unfold E0. rewrite <- (ridx_roundtrip r) at 1.
    pose proof (ridx_range r) as Hlt.
    set (n := ridx r) in *. clearbody n.
    cbn [edenot].
    do 32 (destruct n as [|n]; [reflexivity|]).
    exfalso. lia.
Qed.

(* [comment removed for export] *)
Definition Eplus (regs : bvmap 5 word) (vals : list word) : env :=
  fun n => if Nat.ltb n 32
           then getr regs (Z_to_bv 5 (Z.of_nat n))
           else nth (n - 32) vals (Z_to_bv 64 0).

Lemma regs_ok_Eplus : forall regs vals, regs_ok (Eplus regs vals) sr_id regs.
Proof.
  intros regs vals r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - unfold Eplus. rewrite <- (ridx_roundtrip r) at 1.
    pose proof (ridx_range r) as Hlt.
    set (n := ridx r) in *. clearbody n.
    cbn [edenot].
    do 32 (destruct n as [|n]; [reflexivity|]).
    exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : nat)
| SCDisjoint (a1 : saddr) (n1 : nat) (a2 : saddr) (n2 : nat)
| SCStoreOk  (a : saddr) (n : nat)
| SCReadBase (a : saddr) (n : nat) (e : expr).

(* [comment removed for export] *)
Definition sc_flat (E : env) (a : saddr) (n : nat) : Prop :=
  (0 <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z
  /\ (bv_unsigned (bdenot E (a_base a)) + a_off a < 2^64)%Z
  /\ (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat n <= 2^64)%Z.

Lemma flat_u : forall E a n, sc_flat E a n ->
  bv_unsigned (adenot E a) = (bv_unsigned (bdenot E (a_base a)) + a_off a)%Z.
Proof.
  intros E a n (H1 & H2 & H3). unfold adenot, v_addi.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia.
Qed.

Definition sc_denot (segs : list Segment) (base : word -> option byte)
                    (E : env) (s : sidecond) : Prop :=
  match s with
  | SCBr t c a b => branch_taken c (edenot E a) (edenot E b) = t
  | SCFlat a n => sc_flat E a n
  | SCDisjoint a1 n1 a2 n2 =>
      (bv_unsigned (adenot E a1) + Z.of_nat n1 <= 2^64)%Z
      /\ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= 2^64)%Z
      /\ ((bv_unsigned (adenot E a1) + Z.of_nat n1 <= bv_unsigned (adenot E a2))%Z
          \/ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= bv_unsigned (adenot E a1))%Z)
  | SCStoreOk a n => RiscvSemantics.store_ok segs base (adenot E a) n = true
  | SCReadBase a n e =>
      exists bs, rdn segs base (adenot E a) n = Some bs
                 /\ bytes_le_to_Z bs = bv_unsigned (edenot E e)
  end.

Definition scs_denot (segs : list Segment) (base : word -> option byte)
                     (E : env) (l : list sidecond) : Prop :=
  Forall (sc_denot segs base E) l.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sc_flat_of_region : forall E a n r,
  rg_wf r -> (1 <= n)%nat ->
  (rg_lo r <= bv_unsigned (bdenot E (a_base a)) + a_off a)%Z ->
  (bv_unsigned (bdenot E (a_base a)) + a_off a + Z.of_nat n <= rg_hi r)%Z ->
  sc_flat E a n.
Proof.
  intros E a n r (H0 & H1 & H2) Hn Hl Hh. unfold sc_flat.
  assert (1 <= Z.of_nat n)%Z by lia. repeat split; lia.
Qed.

Lemma sc_disjoint_of_regions : forall segs base E a1 n1 a2 n2 r1 r2,
  rg_wf r1 -> rg_wf r2 -> rg_disj r1 r2 ->
  covers r1 (adenot E a1) n1 -> covers r2 (adenot E a2) n2 ->
  sc_denot segs base E (SCDisjoint a1 n1 a2 n2).
Proof.
  intros segs base E a1 n1 a2 n2 r1 r2 Hw1 Hw2 Hd Hc1 Hc2.
  cbn [sc_denot]. repeat split.
  - exact (covers_nowrap r1 _ _ Hw1 Hc1).
  - exact (covers_nowrap r2 _ _ Hw2 Hc2).
  - exact (covers_disj r1 r2 _ _ _ _ Hd Hc1 Hc2).
Qed.

(* [comment removed for export] *)
Lemma sc_disjoint_same_region : forall segs base E a1 n1 a2 n2 r,
  rg_wf r ->
  covers r (adenot E a1) n1 -> covers r (adenot E a2) n2 ->
  (bv_unsigned (adenot E a1) + Z.of_nat n1 <= bv_unsigned (adenot E a2))%Z
  \/ (bv_unsigned (adenot E a2) + Z.of_nat n2 <= bv_unsigned (adenot E a1))%Z ->
  sc_denot segs base E (SCDisjoint a1 n1 a2 n2).
Proof.
  intros segs base E a1 n1 a2 n2 r Hw Hc1 Hc2 Hd.
  cbn [sc_denot]. repeat split;
    [ exact (covers_nowrap r _ _ Hw Hc1)
    | exact (covers_nowrap r _ _ Hw Hc2)
    | exact Hd ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sm_lookup (log : list sentry) (b : sbase) (k : Z) (n : nat)
  : option (option expr * list sidecond) :=
  match log with
  | [] => Some (None, [])
  | SE (SA b' k') w v :: rest =>
      if sbase_eqb b b' then
        (if (Z.eqb k k' && Nat.eqb n 8 && Nat.eqb w 8)%bool
         then Some (Some v, [])
         else if (Z.leb (k + Z.of_nat n) k' || Z.leb (k' + Z.of_nat w) k)%bool
              then sm_lookup rest b k n
              else None)
      else
        match sm_lookup rest b k n with
        | Some (r, scs) =>
            Some (r, SCDisjoint (SA b k) n (SA b' k') w :: scs)
        | None => None
        end
  end.

Definition msize_bytes (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

(* [comment removed for export] *)
Definition mkSext32 (e : expr) : expr := EAluw ALU_ADD e (ELit 0).

(* [comment removed for export] *)
Definition sym_step (i : instr) (ss : sym_state) (rds : list expr)
  : option (sym_state * list sidecond * list expr) :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm =>
      Some (sset ss rd (mkAlu op (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | ShiftImm op rd rs sh =>
      Some (sset ss rd (mkAlu op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | Op op rd rs1 rs2 =>
      Some (sset ss rd (mkAlu op (g rs1) (g rs2)) (p + 4), [], rds)
  | OpImm32 rd rs imm =>
      Some (sset ss rd (EAluw ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4), [], rds)
  | ShiftImm32 op rd rs sh =>
      Some (sset ss rd (EAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4), [], rds)
  | Op32 op rd rs1 rs2 =>
      Some (sset ss rd (EAluw op (g rs1) (g rs2)) (p + 4), [], rds)
  | Mul op rd rs1 rs2 =>
      Some (sset ss rd (EMd op (g rs1) (g rs2)) (p + 4), [], rds)
  | Mul32 op rd rs1 rs2 =>
      Some (sset ss rd (EMdw op (g rs1) (g rs2)) (p + 4), [], rds)
  | Lui rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12)) (p + 4), [], rds)
  | Auipc rd imm =>
      Some (sset ss rd (ELit (Z.shiftl (bv_signed imm) 12 + p)) (p + 4), [], rds)
  | Jal rd imm =>
      Some (sset ss rd (ELit (p + 4)) (p + bv_signed imm), [], rds)
  | Jalr rd rs1 imm =>
      (* [comment removed for export] *)
      match g rs1 with
      | ELit z => Some (sset ss rd (ELit (p + 4))
                             (Z.land (bv_wrap 64 z + bv_signed imm) (-2)), [], rds)
      | _ => None
      end
  (* [comment removed for export] *)
  | Load sz sgn rd rs imm =>
      let n := msize_bytes sz in
      match to_saddr (g rs) (bv_signed imm) with
      | None => None
      | Some a =>
          match sm_lookup (s_log ss) (a_base a) (a_off a) n with
          | None => None
          | Some (Some v, scs) =>
              (* [comment removed for export] *)
              match sz, sgn with
              | SZ8, true => Some (sset ss rd v (p + 4), SCFlat a 8 :: scs, rds)
              | _, _ => None
              end
          | Some (None, scs) =>
              let i := s_next ss in
              let rv := match rds with [] => EVar i | e :: _ => e end in
              let rds' := match rds with [] => [] | _ :: t => t end in
              let scs' := SCFlat a n :: SCReadBase a n rv :: scs in
              let mk e := Some (SS (p + 4)
                                   (if bv_eqb rd 0 then s_regs ss
                                    else sr_upd (s_regs ss) (ridx rd) e)
                                   (s_log ss) (S i), scs', rds') in
              match sz, sgn with
              | SZ8, true => mk rv
              | SZ4, false => mk rv
              | SZ2, false => mk rv
              | SZ1, false => mk rv
              | SZ4, true => mk (mkSext32 rv)
              | _, _ => None
              end
          end
      end
  (* [comment removed for export] *)
  | Store sz rs1 rs2 imm =>
      match sz with
      | SZ1 | SZ4 | SZ8 =>
          let n := msize_bytes sz in
          match to_saddr (g rs1) (bv_signed imm) with
          | None => None
          | Some a =>
              Some (SS (p + 4) (s_regs ss)
                       (SE a n (g rs2) :: s_log ss) (s_next ss),
                    [SCFlat a n; SCStoreOk a n], rds)
          end
      | _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma b_lw_val : forall v : word, sext 64 (bv_extract 0 32 v) = v_lw v.
Proof.
  intro v. apply bv_eq. unfold sext, v_lw.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned.
  f_equal. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply bv_swrap_wrap.
Qed.

Lemma step_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Lemma alu32_add_0 : forall x : bv 32, alu32 ALU_ADD x (Z_to_bv 32 0) = x.
Proof.
  intro x. change (alu32 ALU_ADD x (Z_to_bv 32 0)) with (x + Z_to_bv 32 0).
  apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  replace (bv_wrap 32 0) with 0%Z by reflexivity.
  rewrite Z.add_0_r. apply bv_wrap_bv_unsigned.
Qed.

Lemma mkSext32_denot : forall E e, edenot E (mkSext32 e) = v_lw (edenot E e).
Proof.
  intros E e. cbn [edenot mkSext32].
  rewrite low32_lit, alu32_add_0. apply b_lw_val.
Qed.

Lemma bytes_le_to_Z_1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof.
  intro b. cbn [bytes_le_to_Z].
  rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shiftr8_mod_pow2 : forall (k z : Z), (0 <= k)%Z ->
  (Z.shiftr (z mod 2 ^ (k + 8)) 8 = (Z.shiftr z 8) mod 2 ^ k)%Z.
Proof.
  intros k z Hk. apply Z.bits_inj'. intros i Hi.
  rewrite Z.shiftr_spec by lia.
  destruct (Z.ltb i k) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma mod_pow2_low : forall (z k m : Z), (0 <= m <= k)%Z ->
  ((z mod 2 ^ k) mod 2 ^ m = z mod 2 ^ m)%Z.
Proof.
  intros z k m Hm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.ltb i m) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_mod : forall (n : nat) (z : Z),
  Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n))%Z = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes]. f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with (2 ^ 8)%Z.
    apply mod_pow2_low. lia.
  - replace (8 * Z.of_nat (S n))%Z with (8 * Z.of_nat n + 8)%Z by lia.
    rewrite shiftr8_mod_pow2 by lia. apply IH.
Qed.

Lemma low32_le_bytes : forall v : word,
  Z_to_le_bytes 4%nat (bv_unsigned (low32 v)) = word_to_le_bytes 4 v.
Proof.
  intro v. unfold word_to_le_bytes, low32.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  change (bv_wrap 32 (bv_unsigned v)) with (bv_unsigned v mod 2 ^ 32)%Z.
  exact (Z_to_le_bytes_mod 4 (bv_unsigned v)).
Qed.

(* [comment removed for export] *)
Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, low32_le_bytes, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Lemma scs_denot_cons : forall base E s l,
  scs_denot segs base E (s :: l) -> sc_denot segs base E s /\ scs_denot segs base E l.
Proof. intros base E s l H. inversion H; auto. Qed.

(* [comment removed for export] *)
Lemma sm_lookup_sound : forall base E log b k n r scs,
  sm_lookup log b k n = Some (r, scs) ->
  scs_denot segs base E scs ->
  log_flat E log ->
  sc_flat E (SA b k) n ->
  match r with
  | None => rdn segs (mem_denot E base log) (adenot E (SA b k)) n
              = rdn segs base (adenot E (SA b k)) n
  | Some v =>
      n = 8%nat /\
      rdn segs (mem_denot E base log) (adenot E (SA b k)) n
        = Some (word_to_le_bytes 8 (edenot E v))
  end.
Proof.
  intros base E log. induction log as [|[[b' k'] w v'] rest IH];
    intros b k n r scs Hl Hsc Hlf Hfl.
  { cbn in Hl. injection Hl as <- <-. reflexivity. }
  cbn [log_flat] in Hlf. destruct Hlf as (Hf1 & Hf2 & Hf3 & Hlf').
  cbn [a_base a_off] in Hf1, Hf2, Hf3.
  pose proof (flat_u E (SA b k) n Hfl) as Hua.
  cbn [a_base a_off] in Hua.
  assert (Hfl2 := Hfl). unfold sc_flat in Hfl2. cbn [a_base a_off] in Hfl2.
  destruct Hfl2 as (Hk1 & Hk2 & Hk3).
  cbn [sm_lookup] in Hl.
  destruct (sbase_eqb b b') eqn:Hb.
  - apply sbase_eqb_eq in Hb. subst b'.
    assert (Hua' : bv_unsigned (adenot E (SA b k')) =
                   (bv_unsigned (bdenot E b) + k')%Z).
    { apply (flat_u E (SA b k') w). unfold sc_flat.
      cbn [a_base a_off]. repeat split; lia. }
    cbn [a_base a_off] in Hua'.
    destruct (Z.eqb k k' && Nat.eqb n 8 && Nat.eqb w 8)%bool eqn:Hhit.
    + injection Hl as <- <-.
      apply andb_prop in Hhit as [Hhit Hw8]. apply andb_prop in Hhit as [Hkk Hn8].
      apply Z.eqb_eq in Hkk. apply Nat.eqb_eq in Hn8. apply Nat.eqb_eq in Hw8.
      subst k' n w. split; [reflexivity|].
      cbn [mem_denot e_addr e_width e_val].
      apply rdn_wbytes_hit8. lia.
    + destruct (Z.leb (k + Z.of_nat n) k' || Z.leb (k' + Z.of_nat w) k)%bool eqn:Hdis;
        [|discriminate].
      assert (Hd : (bv_unsigned (adenot E (SA b k)) + Z.of_nat n
                      <= bv_unsigned (adenot E (SA b k')))%Z
                   \/ (bv_unsigned (adenot E (SA b k')) + Z.of_nat w
                      <= bv_unsigned (adenot E (SA b k)))%Z).
      { apply orb_prop in Hdis as [Hdis|Hdis]; apply Z.leb_le in Hdis;
          [left|right]; lia. }
      specialize (IH b k n r scs Hl Hsc Hlf' Hfl).
      cbn [mem_denot e_addr e_width e_val].
      assert (Hskip : rdn segs (wbytes (mem_denot E base rest)
                                 (adenot E (SA b k'))
                                 (word_to_le_bytes w (edenot E v')))
                          (adenot E (SA b k)) n
                      = rdn segs (mem_denot E base rest) (adenot E (SA b k)) n).
      { destruct Hd as [Hd|Hd].
        - apply rdn_wbytes_below;
            [ lia | rewrite length_N_to_le_bytes; lia ].
        - apply rdn_wbytes_disjoint;
            [ rewrite length_N_to_le_bytes; lia
            | lia ]. }
      destruct r as [v|]; [destruct IH as [Hn8 IH]; split; [exact Hn8|]|];
        rewrite Hskip; exact IH.
  - destruct (sm_lookup rest b k n) as [[r0 scs0]|] eqn:Hrec; [|discriminate].
    injection Hl as <- <-.
    apply scs_denot_cons in Hsc as [Hhd Htl].
    cbn [sc_denot] in Hhd. destruct Hhd as (Hnw1 & Hnw2 & Hd).
    specialize (IH b k n r0 scs0 Hrec Htl Hlf' Hfl).
    cbn [mem_denot e_addr e_width e_val].
    assert (Hskip : rdn segs (wbytes (mem_denot E base rest)
                               (adenot E (SA b' k'))
                               (word_to_le_bytes w (edenot E v')))
                        (adenot E (SA b k)) n
                    = rdn segs (mem_denot E base rest) (adenot E (SA b k)) n).
    { destruct Hd as [Hd|Hd].
      - apply rdn_wbytes_below;
          [ lia | rewrite length_N_to_le_bytes; lia ].
      - apply rdn_wbytes_disjoint;
          [ rewrite length_N_to_le_bytes; lia | lia ]. }
    destruct r0 as [v|]; [destruct IH as [Hn8 IH]; split; [exact Hn8|]|];
      rewrite Hskip; exact IH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sym_step_sound : forall E base rom ss ms i ss' scs w rds rds',
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_step i ss rds = Some (ss', scs, rds') ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms'
              /\ st_ok E base rom ss' ms'.
Proof.
  intros E base rom ss ms i ss' scs w rds rds' Hf He Hd Hs Hsc
    (regs & -> & Hregs & Hlf).
  set (mem := mem_denot E base (s_log ss)) in *.
  destruct i; cbn [sym_step] in Hs; try discriminate.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_lui segs regs _ mem rom w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs | reflexivity].
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_auipc segs regs _ mem rom w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. symmetry. apply v_auipc_lit.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_jal_link segs regs _ mem rom w rd imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply btgt_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. symmetry. apply v_addi_lit.
  - (* [comment removed for export] *)
    destruct (sr_get (s_regs ss) rs1) as [z| | | | |] eqn:Hg; try discriminate.
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_jalr segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
    eexists; split.
    + f_equal. cbn [s_pc sset]. unfold v_jalr.
      specialize (Hregs rs1) as Hg1. rewrite Hg in Hg1. cbn [edenot] in Hg1.
      rewrite Hg1. exact (jalr_tgt_lit z (bv_signed imm)).
    + cbn [s_regs s_log sset]. split; [| exact Hlf].
      apply regs_ok_upd; [exact Hregs|].
      cbn [edenot]. symmetry. apply v_addi_lit.
  - (* [comment removed for export] *)
    destruct (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm)) as [a|] eqn:Ha;
      [|discriminate].
    assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm))
      by (rewrite (to_saddr_denot E _ _ _ Ha), Hregs; reflexivity).
    destruct a as [ab ak]; cbn [a_base a_off] in *.
    destruct (sm_lookup (s_log ss) ab ak (msize_bytes sz))
      as [[[v|] scs0]|] eqn:Hlk; [| |discriminate].
    + (* [comment removed for export] *)
      destruct sz; try discriminate; destruct signed; try discriminate.
      injection Hs as <- <- <-.
      apply scs_denot_cons in Hsc as [Hfit Hsc0]. cbn [sc_denot] in Hfit.
      destruct (sm_lookup_sound base E (s_log ss) ab ak 8%nat (Some v) scs0
                  Hlk Hsc0 Hlf Hfit) as [_ Hread].
      rewrite Hadr in Hread.
      eexists; split;
        [ exact (step_ld segs regs _ mem rom w rd rs1 imm _ (edenot E v)
                   Hf He Hd Hread (bytes_le_to_Z_8 _)) |].
      eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
      cbn [s_regs s_log sset]. split; [| exact Hlf].
      apply regs_ok_upd; [exact Hregs | reflexivity].
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      set (rv := match rds with [] => EVar (s_next ss) | e :: _ => e end) in *.
      assert (Hshape :
        scs = SCFlat (SA ab ak) (msize_bytes sz)
                :: SCReadBase (SA ab ak) (msize_bytes sz) rv :: scs0
        /\ ss' = SS (s_pc ss + 4)
                    (if bv_eqb rd 0 then s_regs ss
                     else sr_upd (s_regs ss) (ridx rd)
                            (match sz, signed with
                             | SZ4, true => mkSext32 rv
                             | _, _ => rv
                             end))
                    (s_log ss) (S (s_next ss))).
      { unfold rv; destruct rds; destruct sz; destruct signed; cbn in Hs;
          try discriminate; injection Hs as <- <- <-; split; reflexivity. }
      destruct Hshape as [-> ->].
      apply scs_denot_cons in Hsc as [Hfit Hsc1].
      apply scs_denot_cons in Hsc1 as [Hrb Hsc0].
      cbn [sc_denot] in Hfit, Hrb.
      destruct Hrb as (bs & Hrdn & Hbs).
      pose proof (sm_lookup_sound base E (s_log ss) ab ak (msize_bytes sz)
                    None scs0 Hlk Hsc0 Hlf Hfit) as Hmiss.
      rewrite Hadr in Hmiss, Hrdn.
      assert (Hread : rdn segs mem (v_addi (getr regs rs1) (bv_signed imm))
                        (msize_bytes sz) = Some bs)
        by (unfold mem; rewrite Hmiss; exact Hrdn).
      clear Hmiss Hrdn. rename Hread into Hrdn.
      pose proof (rdn_length segs mem _ _ _ Hrdn) as Hlen.
      (* [comment removed for export] *)
      destruct sz; destruct signed; cbn in Hs; try discriminate; clear Hs.
      * (* [comment removed for export] *)
        destruct bs as [|b0 [|??]]; cbn in Hlen; try discriminate.
        rewrite bytes_le_to_Z_1 in Hbs.
        eexists; split;
          [ exact (step_lbu segs regs _ mem rom w rd rs1 imm b0 Hf He Hd Hrdn) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs|].
        rewrite Hbs. symmetry. apply Z_to_bv_bv_unsigned.
      * (* [comment removed for export] *)
        eexists; split;
          [ exact (step_lhu segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs | reflexivity].
      * (* [comment removed for export] *)
        eexists; split;
          [ exact (step_lw segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs|].
        rewrite mkSext32_denot. reflexivity.
      * (* [comment removed for export] *)
        eexists; split;
          [ exact (step_lwu segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs | reflexivity].
      * (* [comment removed for export] *)
        eexists; split;
          [ exact (step_ld segs regs _ mem rom w rd rs1 imm bs (edenot E rv)
                     Hf He Hd Hrdn Hbs) |].
        eexists; split; [ f_equal; cbn [s_pc]; apply v_addi_lit |].
        cbn [s_regs s_log]. split; [| exact Hlf].
        apply regs_ok_upd; [exact Hregs | reflexivity].
  - (* [comment removed for export] *)
    destruct sz; try discriminate;
      destruct (to_saddr (sr_get (s_regs ss) rs1) (bv_signed imm)) as [a|] eqn:Ha;
      try discriminate; injection Hs as <- <- <-;
      (assert (Hadr : adenot E a = v_addi (getr regs rs1) (bv_signed imm))
         by (rewrite (to_saddr_denot E _ _ _ Ha), Hregs; reflexivity));
      apply scs_denot_cons in Hsc as [Hfl Hsc1];
      apply scs_denot_cons in Hsc1 as [Hok _];
      cbn [sc_denot] in Hfl, Hok;
      rewrite Hadr in Hok;
      (assert (Hok' : RiscvSemantics.store_ok segs mem
                        (v_addi (getr regs rs1) (bv_signed imm)) _ = true)
         by (eapply store_ok_mono; [ apply mem_denot_grows | exact Hok ])).
    + (* [comment removed for export] *)
      eexists; split;
        [ exact (step_sb segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok') |].
      eexists; split.
      * f_equal; [ cbn [s_pc]; apply v_addi_lit |].
        cbn [s_log mem_denot e_addr e_width e_val].
        rewrite Hadr, (Hregs rs2). reflexivity.
      * cbn [s_regs s_log]. split; [exact Hregs|].
        cbn [log_flat]. destruct Hfl as (H1 & H2 & H3). repeat split; assumption.
    + (* [comment removed for export] *)
      eexists; split;
        [ exact (step_sw_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok') |].
      eexists; split.
      * f_equal; [ cbn [s_pc]; apply v_addi_lit |].
        cbn [s_log mem_denot e_addr e_width e_val].
        rewrite Hadr, (Hregs rs2). reflexivity.
      * cbn [s_regs s_log]. split; [exact Hregs|].
        cbn [log_flat]. destruct Hfl as (H1 & H2 & H3). repeat split; assumption.
    + (* [comment removed for export] *)
      eexists; split;
        [ exact (step_sd_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok') |].
      eexists; split.
      * f_equal; [ cbn [s_pc]; apply v_addi_lit |].
        cbn [s_log mem_denot e_addr e_width e_val].
        rewrite Hadr, (Hregs rs2). reflexivity.
      * cbn [s_regs s_log]. split; [exact Hregs|].
        cbn [log_flat]. destruct Hfl as (H1 & H2 & H3). repeat split; assumption.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_opimm_gen segs regs _ mem rom w op rd rs1 imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    rewrite mkAlu_denot. cbn [edenot]. rewrite <- Hregs, sext64_lit. reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_shiftimm_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    rewrite mkAlu_denot. cbn [edenot]. rewrite <- Hregs, zext64_lit. reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_op_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    rewrite mkAlu_denot. rewrite <- !Hregs. reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_opimm32_gen segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- Hregs, (sext32_low32 imm). reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_shiftimm32_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- Hregs, (zext32_low32 shamt). reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_op32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- !Hregs. reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_mul_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- !Hregs. reflexivity.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_mul32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd) |].
    eexists; split; [ f_equal; cbn [s_pc sset]; apply v_addi_lit |].
    cbn [s_regs s_log sset]. split; [| exact Hlf].
    apply regs_ok_upd; [exact Hregs|].
    cbn [edenot]. rewrite <- !Hregs. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint sym_exec (fuel : nat) (dirs : list bool) (rds : list expr)
                  (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond :=
  match fuel with
  | O => (ss, acc)
  | S f =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => (ss, acc)
      | Some w =>
          if is_ecall w then (ss, acc) else
          match decode_any w with
          | None => (ss, acc)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (ss, acc) else
              match i with
              | Branch c rs1 rs2 imm =>
                  match dirs with
                  | [] => (ss, acc)
                  | t :: dirs' =>
                      sym_exec f dirs' rds
                        (sjump ss (if t then (s_pc ss + bv_signed imm)%Z
                                   else (s_pc ss + 4)%Z))
                        (SCBr t c (sr_get (s_regs ss) rs1)
                                  (sr_get (s_regs ss) rs2) :: acc)
                  end
              | _ =>
                  match sym_step i ss rds with
                  | Some (ss', scs, rds') => sym_exec f dirs rds' ss' (scs ++ acc)
                  | None => (ss, acc)
                  end
              end
          end
      end
  end.

(* [comment removed for export] *)
Lemma sym_exec_acc : forall fuel dirs rds ss acc,
  exists pre, snd (sym_exec fuel dirs rds ss acc) = pre ++ acc.
Proof.
  induction fuel as [|f IH]; intros dirs rds ss acc; [exists []; reflexivity|].
  cbn [sym_exec].
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|exists []; reflexivity].
  destruct (is_ecall w); [exists []; reflexivity|].
  destruct (decode_any w) as [[i sz]|] eqn:Hdec; [|exists []; reflexivity].
  destruct (Z.eqb sz 4); cbn [negb]; [|exists []; reflexivity].
  destruct i;
    try (match goal with
         | |- context [ sym_step ?ii ss rds ] =>
             destruct (sym_step ii ss rds) as [[[ss2 scs2] rds2]|] eqn:Hstep;
               [ destruct (IH dirs rds2 ss2 (scs2 ++ acc)) as [pre Hpre];
                 exists (pre ++ scs2); rewrite <- app_assoc; exact Hpre
               | exists []; reflexivity ]
         end).
  (* [comment removed for export] *)
  destruct dirs as [|t dirs']; [exists []; reflexivity|].
  destruct (IH dirs' rds (sjump ss (if t then (s_pc ss + bv_signed imm)%Z
                                else (s_pc ss + 4)%Z))
                     (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc))
    as [pre Hpre].
  exists (pre ++ [SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2)]).
  rewrite <- app_assoc. exact Hpre.
Qed.

Lemma scs_denot_app : forall base E l1 l2,
  scs_denot segs base E (l1 ++ l2) ->
  scs_denot segs base E l1 /\ scs_denot segs base E l2.
Proof.
  intros base E l1 l2 H. unfold scs_denot in *.
  split; apply Forall_forall; intros x Hx;
    rewrite Forall_forall in H; apply H, in_or_app; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sym_exec_sound : forall fuel dirs rds ss acc ss' scs E base rom ms,
  sym_exec fuel dirs rds ss acc = (ss', scs) ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok E base rom ss' ms'.
Proof.
  induction fuel as [|f IH]; intros dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst.
  { cbn in Hex. injection Hex as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  assert (Hstop : (ss, acc) = (ss', scs) ->
                  exists ms', msteps segs ms ms' /\ st_ok E base rom ss' ms').
  { intro HX. injection HX as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  cbn [sym_exec] in Hex.
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|exact (Hstop Hex)].
  destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
  destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
  apply Z.eqb_eq in Hsz. subst sz.
  destruct i;
    try (match type of Hex with
         | context [ sym_step ?ii ss rds ] =>
             destruct (sym_step ii ss rds) as [[[ss2 scs2] rds2]|] eqn:Hstep;
               [|exact (Hstop Hex)];
             destruct (sym_exec_acc f dirs rds2 ss2 (scs2 ++ acc)) as [pre Hpre];
             rewrite Hex in Hpre; cbn [snd] in Hpre; subst scs;
             assert (Hsc2 : scs_denot segs base E scs2)
               by (apply scs_denot_app in Hsc as [_ Hsc];
                   apply scs_denot_app in Hsc as [Hsc _]; exact Hsc);
             assert (Hsc' : scs_denot segs base E (pre ++ (scs2 ++ acc)))
               by exact Hsc;
             destruct (sym_step_sound E base rom ss ms ii ss2 scs2 w rds rds2
                         Hf He Hd Hstep Hsc2 Hst)
               as (msA & HstepA & HstA);
             destruct (IH dirs rds2 ss2 (scs2 ++ acc) ss' _ E base rom msA
                         Hex Hsc' HstA)
               as (msB & HmsB & HstB);
             exists msB; split; [| exact HstB];
             eapply mst_step;
               [ destruct Hst as (rr & -> & _); reflexivity
               | exact HstepA | exact HmsB ]
         end).
  (* [comment removed for export] *)
  destruct dirs as [|t dirs']; [exact (Hstop Hex)|].
  destruct Hst as (regs & -> & Hregs & Hlf).
  destruct (sym_exec_acc f dirs' rds
              (sjump ss (if t then (s_pc ss + bv_signed imm)%Z else (s_pc ss + 4)%Z))
              (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2) :: acc))
    as [pre Hpre].
  rewrite Hex in Hpre. cbn [snd] in Hpre. subst scs.
  assert (Hhd : sc_denot segs base E
                  (SCBr t c (sr_get (s_regs ss) rs1) (sr_get (s_regs ss) rs2))).
  { apply scs_denot_app in Hsc as [_ Hsc]. inversion Hsc; assumption. }
  cbn [sc_denot] in Hhd.
  rewrite <- !Hregs in Hhd.
  assert (HstA : st_ok E base rom
                   (sjump ss (if t then (s_pc ss + bv_signed imm)%Z else (s_pc ss + 4)%Z))
                   (mkst regs (if t then btgt (Z_to_bv 64 (s_pc ss)) (bv_signed imm)
                               else v_addi (Z_to_bv 64 (s_pc ss)) 4)
                         (mem_denot E base (s_log ss)) rom)).
  { eexists; split; [| split; [exact Hregs | exact Hlf]].
    cbn [s_pc s_log sjump]. destruct t; [rewrite btgt_lit | rewrite v_addi_lit]; reflexivity. }
  destruct (IH dirs' rds _ _ ss' _ E base rom _ Hex Hsc HstA) as (msB & HmsB & HstB).
  exists msB. split; [| exact HstB].
  eapply mst_step; [ reflexivity | | exact HmsB ].
  destruct t.
  - exact (step_branch_tk_gen segs regs _ (mem_denot E base (s_log ss)) rom
             w c rs1 rs2 imm Hf He Hd Hhd).
  - exact (step_branch_ft_gen segs regs _ (mem_denot E base (s_log ss)) rom
             w c rs1 rs2 imm Hf He Hd Hhd).
Qed.

(* [comment removed for export] *)
Lemma sym_exec_msteps : forall fuel dirs rds ss ss' scs E base rom ms,
  sym_exec fuel dirs rds ss [] = (ss', scs) ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok E base rom ss' ms'.
Proof. intros. eapply sym_exec_sound; eauto. Qed.

(* [comment removed for export] *)
Theorem sym_exec_ex : forall fuel dirs rds ss acc ss' scs E base rom ms,
  sym_exec fuel dirs rds ss acc = (ss', scs) ->
  scs_denot segs base E scs ->
  st_ok E base rom ss ms ->
  exists R, regs_ok E (s_regs ss') R
         /\ msteps segs ms (mkst R (Z_to_bv 64 (s_pc ss'))
                                 (mem_denot E base (s_log ss')) rom).
Proof.
  intros fuel dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst.
  destruct (sym_exec_sound fuel dirs rds ss acc ss' scs E base rom ms Hex Hsc Hst)
    as (ms' & Hms & (R & Heq & Hregs & _)).
  exists R. split; [exact Hregs|]. rewrite <- Heq. exact Hms.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP1.
Ltac sym_val_norm :=
  cbn [edenot sr_get nth ridx bv_eqb s_regs s_pc];
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra.
