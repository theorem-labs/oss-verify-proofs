(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (33 recorded proofs replaced by written proofs (nret_strip_ci, errno_of_Some, errno_of_errno_ret and 30 more); nstep_dec_munmap restated for the revision's model; nstep_dec_read, nstep_dec_mmap, nstep_dec_mmap_none and 1 more re-proved; adds iv_subtract_outside, maps_subtract_exact, check_munmap_exact_grant). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Decode () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib5Lists7ListDef3mapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib3Lib5Nodes4eff0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes6efferrC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z9leb_spec0C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes7reflect00K47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retK47Corelib7Numbers7BinNums1Z03C57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z3oppC45stdpp9bitvector;definitions7bv_wrapC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedK47Corelib4Init5Logic3and01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indK47Corelib4Init9Datatypes6option01C57Corelib7BinNums6PosDef3Pos3mulC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_unsignedC4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode>errno_of_smallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode9dec_plainC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode9efferr_ciC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode7eff0_ciC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00k59OSSVerify5KrLib3Lib6Decode4sret01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode=errno_of_SomeC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode4sret02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4list02i59OSSVerify5KrLib3Lib6Decode4sret00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib3Lib6DecodeBerrno_of_errno_retC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode<errno_of_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode8dec_readC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode8read_ans01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode8read_ans02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4andbC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess@delivered_writesC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z3eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03i59OSSVerify5KrLib3Lib6Decode8read_ans00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib3Lib6Decode9dec_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode:dec_count0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode:dec_writevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode?dec_count0_SomeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01c59OSSVerify5KrLib3Lib6Decode>dec_count_SomeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib3Lib6Decode;dec_set_tidC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbC6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEc59OSSVerify5KrLib3Lib6Decode8dec_brk0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode7dec_brkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode=brk_new_pagesC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqc59OSSVerify5KrLib3Lib6Decode8zeros_ofC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib3Lib6Decode7brk_ans00C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode7brk_ans02C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode7brk_ans01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode6avoidsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3orbC46Stdlib5Lists4List7forallbC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List>forallb_forallC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib3Lib6Decode8dec_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode8mmap_ans01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode8mmap_ans02C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode=dec_mmap_noneC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode:dec_munmapC1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode<dec_mprotectC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode;dec_madviseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6DecodeAdec_mprotect_SomeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List=length_firstnC4ELinuxProcessSemantics?LinuxProcessSem2Fs9file_readC4ELinuxProcessSemantics?LinuxProcessSem2FsCfile_read_unguardedK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01c59OSSVerify5KrLib3Lib6DecodeIlength_file_read_le_countC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z8eqb_reflC59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry03K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry04K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry05K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry07K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry08K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry09C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_insertC4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem5State5event00C4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRC4ELinuxProcessSemantics?LinuxProcessSem5State5EBADFK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06I4ELinuxProcessSemantics?LinuxProcessSem5State9SockState00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry0:K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State5event02c59OSSVerify5KrLib3Lib6Decode9dec_writeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6concatK59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega5Tauto8GFormula02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open=openat_errnosC59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs4Open>path_is_dirrefC59OSSVerify5KrLib3Lib5Nodes;open_resultC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8alloc_fdc59OSSVerify5KrLib3Lib6Decode=dec_plain_errC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6DecodeCopenat_errnos_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode8dec_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>alloc_fd_rangeC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init9Datatypes?andb_true_introc59OSSVerify5KrLib3Lib6Decode=dec_plain_valC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3lebC4ELinuxProcessSemantics?LinuxProcessSem5State8path_maxC4ELinuxProcessSemantics?LinuxProcessSem5State<ENAMETOOLONGC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOENTK59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode9dec_closeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_removeK59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode9dec_ioctlC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOTTYC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes@nstep_mm_vm_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=nstep_brk_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z:ltb_irreflC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_page_rangeC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>brk_model_nextC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=with_brk_nextC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State9vmst_mapsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@forget_vm_rangesC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap9check_brkC4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgI6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00C59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib3Lib6DecodeIm_vmmaps_forget_vm_rangesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okC59OSSVerify5KrLib3Lib5Nodes9w_is0_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib6ZArith6BinInt1Z6ltb_gec59OSSVerify5KrLib3Lib6DecodeDpage_round_up_Z_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool<andb_false_rc59OSSVerify5KrLib3Lib6DecodeDvm_brk_with_brk_nextC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapc59OSSVerify5KrLib3Lib6Decode7coveredC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallc59OSSVerify5KrLib3Lib6Decode>region_free_InC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool>orb_true_introC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topK59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib6Decode>mmap_len_boundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC59OSSVerify5KrLib3Lib5Nodes>nstep_mmap_iffC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAerrno_ret_in_trueC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdK4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01c59OSSVerify5KrLib3Lib6DecodeEavoids_of_region_freeC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTc59OSSVerify5KrLib3Lib6Decode@mmap_flags_plainC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_NONEK59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC59OSSVerify5KrLib3Lib5Nodes@nstep_munmap_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeEcheck_ret_only_ok_iffC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterc59OSSVerify5KrLib3Lib6DecodeLm_vmmaps_with_mmap_destroyedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEK59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesBnstep_mprotect_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectImprotect_grows_conflict_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosK59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseEmadvise_dontneed_nextC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm7Madvise=check_madviseC59OSSVerify5KrLib3Lib5NodesAnstep_madvise_iffC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseBmadvise_dontneed_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_ok".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nret_strip_ci : forall ms r ws zs us cs ci,
  nret ms (mkEffectU r ws zs us cs ci) = nret ms (mkEffectU r ws zs us cs []).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition eff0_ci (ci : list (word * nat)) (r : word) : resp := mkEffectU r [] [] [] [] ci.
Definition efferr_ci (ci : list (word * nat)) (e : Z) : resp := eff0_ci ci (errno_ret e).
Lemma eff0_ci_nil : forall r, eff0_ci [] r = eff0 r.
Proof.
ltac2:(KReplay.run1 (kr_t_Decode ()) [] "h01rp;1p;2g006oj10Tg007Tj14Tg0082j12Tg00?Cj11Tg00;fj23Tg00=G#0#0#0#0#0#0#4#2g00@6f0#1'3W0o"). Qed.
Lemma efferr_ci_nil : forall e, efferr_ci [] e = efferr e.
Proof.
ltac2:(KReplay.run1 (kr_t_Decode ()) [] "h01ep;1p;2g00@ij11Tg00;fj20Tg00A^g00@6f0#1'0W0o"). Qed.

(* [comment removed for export] *)
Definition errno_of (r : word) : option Z :=
  if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

Lemma errno_of_Some : forall r e, errno_of r = Some e -> r = errno_ret e /\ (1 <= e <= 4095)%Z.
Proof.
  intros r e H. unfold errno_of in H. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [|discriminate]. inversion H; subst.
  split; [|lia]. apply bv_eq. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
  replace (- (2 ^ 64 - bv_unsigned r))%Z with (bv_unsigned r + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma errno_of_errno_ret : forall e, (1 <= e <= 4095)%Z -> errno_of (errno_ret e) = Some e.
Proof.
  intros e He. unfold errno_of. rewrite errno_ret_unsigned by lia. unfold two_pow_64.
  destruct (Z.leb_spec0 (2^64 - 4095) (2^64 - e)); [|lia]. f_equal. lia.
Qed.

Lemma errno_of_small : forall r, (bv_unsigned r <= 2^64 - 4096)%Z -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia|reflexivity]. Qed.

Lemma errno_of_lit : forall z, (0 <= z <= 2^64 - 4096)%Z -> errno_of (Z_to_bv 64 z) = None.
Proof. intros. apply errno_of_small. rewrite unsigned_lit by lia. lia. Qed.

(* [comment removed for export] *)
Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

(* [comment removed for export] *)
Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with
      | Some e => Some (SErr e)
      | None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
      end
  | _ => None
  end.

Lemma dec_plain_Some : forall ok rsp a, dec_plain ok rsp = Some a ->
  exists ci,
  match a with
  | SErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | SVal v => rsp = eff0_ci ci (Z_to_bv 64 v) /\ ok v = true /\ (0 <= v <= 2^64 - 4096)%Z
  end.
Proof.
  intros ok [r ws zs us cs ci] a H. unfold dec_plain in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  exists ci. destruct (errno_of r) as [e|] eqn:E.
  - inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
  - destruct (ok (bv_unsigned r)) eqn:Hok; [|discriminate]. inversion H; subst.
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
    unfold errno_of in E. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [discriminate|].
    unfold eff0_ci. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; try exact Hok; lia.
Qed.

Lemma dec_plain_err : forall ok ci e, (1 <= e <= 4095)%Z -> dec_plain ok (efferr_ci ci e) = Some (SErr e).
Proof. intros ok ci e He. unfold dec_plain, efferr_ci, eff0_ci. rewrite errno_of_errno_ret by lia. reflexivity. Qed.

Lemma dec_plain_val : forall ok ci z, (0 <= z <= 2^64 - 4096)%Z -> ok z = true ->
  dec_plain ok (eff0_ci ci (Z_to_bv 64 z)) = Some (SVal z).
Proof.
  intros ok ci z Hz Hok. unfold dec_plain, eff0_ci. rewrite errno_of_lit by lia.
  rewrite unsigned_lit by lia. rewrite Hok. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | mkEffectU r [(a, bs)] [] [] [] _ =>
      if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
         && (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some (RdData bs) else None
  | _ => None
  end.

Lemma dec_read_Some : forall buf count rsp a, (0 <= count)%Z -> dec_read buf count rsp = Some a ->
  exists ci,
  match a with
  | RdErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | RdData bs => rsp = mkEffectU (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) [] [] [] ci
                 /\ (Z.of_nat (length bs) <= count)%Z
  end.
Proof.
  intros buf count [r ws zs us cs ci] a Hc H. unfold dec_read in H.
  destruct ws as [|[a0 bs] [|? ?]]; try discriminate.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. exists ci.
    destruct (errno_of r) as [e|] eqn:E.
    + inversion H; subst. apply errno_of_Some in E as [-> He]. split; [reflexivity|exact He].
    + destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst. cbn.
      split; [|lia]. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. exists ci.
    destruct (bv_eqb a0 (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
    destruct (Z.leb_spec0 1 (Z.of_nat (length bs))); [|discriminate].
    destruct (Z.leb_spec0 (Z.of_nat (length bs)) count); [|discriminate].
    destruct (Z.eqb_spec (bv_unsigned r) (Z.of_nat (length bs))); [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. subst a0.
    destruct bs as [|b bs']; [cbn in *; lia|]. cbn [delivered_writes]. split; [|lia].
    f_equal. apply bv_eq. rewrite unsigned_lit. { assumption. }
    pose proof (bv_unsigned_in_range 64 r). unfold bv_modulus in *. lia.
Qed.

(* [comment removed for export] *)
Definition dec_count (count : Z) (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      if (1 <=? bv_unsigned r)%Z && (bv_unsigned r <=? count)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.
Definition dec_write := dec_count.

Definition dec_count0 (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => if (bv_unsigned r =? 0)%Z then Some 0%Z else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition dec_writev (total : Z) (rsp : resp) : option Z :=
  if (total =? 0)%Z then dec_count0 rsp else dec_count total rsp.

Lemma dec_count_Some : forall count rsp k, dec_count count rsp = Some k ->
  exists ci, rsp = eff0_ci ci (Z_to_bv 64 k) /\ (1 <= k <= count)%Z /\ (k < 2^64)%Z.
Proof.
  intros count [r ws zs us cs ci] k H. unfold dec_count in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (Z.leb_spec0 1 (bv_unsigned r)); [|discriminate]. destruct (Z.leb_spec0 (bv_unsigned r) count); [|discriminate].
  inversion H; subst. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  exists ci. unfold eff0_ci. rewrite Z_to_bv_bv_unsigned. repeat split; try reflexivity; lia.
Qed.

Lemma dec_count0_Some : forall rsp k, dec_count0 rsp = Some k ->
  exists ci, k = 0%Z /\ rsp = eff0_ci ci (Z_to_bv 64 0).
Proof.
  intros [r ws zs us cs ci] k H. unfold dec_count0 in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
  exists ci. split; [reflexivity|]. unfold eff0_ci. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_writev_Some : forall total rsp k, dec_writev total rsp = Some k ->
  exists ci, rsp = eff0_ci ci (Z_to_bv 64 k) /\ (k < 2^64)%Z /\
    ((total = 0 /\ k = 0) \/ (total <> 0 /\ 1 <= k <= total))%Z.
Proof.
  intros total rsp k H. unfold dec_writev in H. destruct (Z.eqb_spec total 0).
  - apply dec_count0_Some in H as (ci & -> & ->). exists ci. split; [reflexivity|]. split; [lia|]. left; lia.
  - apply dec_count_Some in H as (ci & -> & Hk & Hk2). exists ci. split; [reflexivity|]. split; [lia|]. right; lia.
Qed.

(* [comment removed for export] *)
Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).
(* [comment removed for export] *)
Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).
(* [comment removed for export] *)
Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).
(* [comment removed for export] *)
Definition dec_set_tid (rsp : resp) : option Z :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition dec_exit (rsp : resp) : option Empty_set := None.

Lemma dec_set_tid_Some : forall rsp t, dec_set_tid rsp = Some t ->
  exists ci, rsp = eff0_ci ci (Z_to_bv 64 t) /\ (0 < t < PID_MAX_ENVELOPE)%Z.
Proof.
  intros [r ws zs us cs ci] t H. unfold dec_set_tid in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  destruct (Z.ltb_spec0 0 (bv_unsigned r)); [|discriminate].
  destruct (Z.ltb_spec0 (bv_unsigned r) PID_MAX_ENVELOPE); [|discriminate]. inversion H; subst.
  exists ci. unfold eff0_ci. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition dec_brk0 (rsp : resp) : option Z :=
  match rsp with mkEffectU r [] [] [] [] _ => Some (bv_unsigned r) | _ => None end.

Lemma dec_brk0_Some : forall rsp b, dec_brk0 rsp = Some b -> exists ci, rsp = eff0_ci ci (Z_to_bv 64 b) /\ (0 <= b < 2^64)%Z.
Proof.
  intros [r ws zs us cs ci] b H. unfold dec_brk0 in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  inversion H; subst. pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R.
  exists ci. unfold eff0_ci. rewrite Z_to_bv_bv_unsigned. split; [reflexivity|lia].
Qed.

(* [comment removed for export] *)
Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
  let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
  if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.

Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
  match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
  match rsp with
  | mkEffectU r [] zs [] [] _ =>
      if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
      else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end.

Lemma dec_brk_Some : forall cur req rsp a, dec_brk cur req rsp = Some a ->
  exists ci,
  match a with
  | BrkSame => rsp = eff0_ci ci (Z_to_bv 64 cur)
  | BrkGrown => rsp = mkEffectU (Z_to_bv 64 req) [] (zeros_of (brk_new_pages cur req)) [] [] ci
  end.
Proof.
  intros cur req [r ws zs us cs ci] a H. unfold dec_brk in H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate]. destruct cs; [|destruct zs; discriminate]. exists ci.
  destruct (Z.eqb_spec (bv_unsigned r) cur).
  - destruct zs.
    + cbn [andb] in H. inversion H; subst. unfold eff0_ci. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
      destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
      rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [andb] in H. destruct (Z.eqb_spec (bv_unsigned r) req); [|discriminate].
    destruct (listNN_eqb _ _) eqn:E; [|discriminate]. inversion H; subst. apply listNN_eqb_eq in E.
    rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Definition mmap_addr_ok (atop len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? atop)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (atop len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [(a, n)] [] [] _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok atop len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Definition dec_mmap_none (atop len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [] [(a, n)] [] _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok atop len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end.

Lemma avoids_In : forall a n avoid lo hi, avoids a n avoid = true -> In (lo, hi) avoid -> (a + n <= lo \/ hi <= a)%Z.
Proof.
  intros a n avoid lo hi H Hin. unfold avoids in H. rewrite forallb_forall in H.
  specialize (H _ Hin). cbn in H. apply orb_prop in H as [H|H]; [left|right]; apply Z.leb_le; exact H.
Qed.

Lemma mmap_addr_ok_true : forall atop len avoid a, mmap_addr_ok atop len avoid a = true ->
  (a mod page_size = 0 /\ 0 < a /\ a + mmap_len len <= atop)%Z /\ avoids a (mmap_len len) avoid = true.
Proof.
  intros atop len avoid a H. unfold mmap_addr_ok in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.

Lemma dec_mmap_Some : forall atop len avoid rsp x, dec_mmap atop len avoid rsp = Some x ->
  exists ci,
  match x with
  | MmErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci /\ mmap_addr_ok atop len avoid a = true
  end.
Proof.
  intros atop len avoid [r ws zs us cs ci] x H. unfold dec_mmap in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. exists ci. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst.
    apply errno_of_Some in E as [-> He]. auto.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. exists ci.
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok atop len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

Lemma dec_mmap_none_Some : forall atop len avoid rsp x, dec_mmap_none atop len avoid rsp = Some x ->
  exists ci,
  match x with
  | MmErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | MmOk a => rsp = mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] ci /\ mmap_addr_ok atop len avoid a = true
  end.
Proof.
  intros atop len avoid [r ws zs us cs ci] x H. unfold dec_mmap_none in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct cs; [|discriminate]. exists ci. destruct (errno_of r) eqn:E; [|discriminate]. inversion H; subst. apply errno_of_Some in E as [-> He]. auto.
  - destruct cs; [|discriminate]. exists ci.
    destruct (bv_eqb a r) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    destruct (mmap_addr_ok atop len avoid (bv_unsigned r)) eqn:E3; [|discriminate]. cbn [andb] in H. inversion H; subst.
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. unfold wa. rewrite Z_to_bv_bv_unsigned. auto.
Qed.

(* [comment removed for export] *)
Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [] [(a, n)] [] _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [(a, n)] [] [] _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition dec_madvise (addr len : Z) (rsp : resp) : option range_ans := dec_mprotect addr len rsp.

Lemma dec_munmap_Some : forall addr len rsp x, dec_munmap addr len rsp = Some x ->
  exists ci,
  match x with
  | RgErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0_ci ci (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] ci
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_munmap in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us as [|[a n] [|? ?]]; try discriminate.
  - destruct cs; [|discriminate]. exists ci. destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0_ci. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct cs; [|discriminate]. exists ci. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_mprotect_Some : forall addr len rsp x, dec_mprotect addr len rsp = Some x ->
  exists ci,
  match x with
  | RgErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0_ci ci (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [] ci
  end.
Proof.
  intros addr len [r ws zs us cs ci] x H. unfold dec_mprotect in H.
  destruct ws; [|discriminate]. destruct zs as [|[a n] [|? ?]]; try discriminate.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. exists ci.
    destruct (errno_of r) eqn:E. { inversion H; subst. apply errno_of_Some in E as [-> He]. auto. }
    destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate]. inversion H; subst.
    unfold eff0_ci. f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. exists ci. destruct (Z.eqb_spec (bv_unsigned r) 0); [|discriminate].
    destruct (bv_eqb a _) eqn:E1; [|discriminate]. destruct (bv_eqb n _) eqn:E2; [|discriminate].
    cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst.
    f_equal. apply bv_eq. rewrite unsigned_lit by lia. assumption.
Qed.

Lemma dec_madvise_Some : forall addr len rsp x, dec_madvise addr len rsp = Some x ->
  exists ci,
  match x with
  | RgErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
  | RgDone false => rsp = eff0_ci ci (Z_to_bv 64 0)
  | RgDone true => rsp = mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (mmap_len len))] [] [] ci
  end.
Proof. intros addr len rsp x H. exact (dec_mprotect_Some addr len rsp x H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_file_read_le_count : forall data off count,
  (0 <= count < 2^64)%Z -> (Z.of_nat (length (file_read data off (Z_to_bv 64 count))) <= count)%Z.
Proof.
  intros data off count Hc. rewrite file_read_unguarded. rewrite length_firstn.
  unfold word_to_nat. rewrite unsigned_lit by lia. lia.
Qed.

Lemma nstep_dec_read : forall fd buf count mo rsp mo' evs,
  (0 <= count < 2^64)%Z ->
  nstep (NRead fd buf count) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_read buf count rsp = Some a /\
  match a with
  | RdErr e => mo' = mo /\
      ((e = EBADF /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None)
       \/ (e = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir))
  | RdData bs => exists p off data,
      fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\
      fs_lookup (m_fs mo) p = Some data /\
      bs = file_read data off (Z_to_bv 64 count) /\
      mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo
  end.
Proof.
  intros fd buf count mo rsp mo' evs Hc [-> H]. split; [reflexivity|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|pid pw|rd wr| |sid sd sst|ectx|fam|aid af]|] eqn:Hlk; try contradiction.
  - destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. destruct H as [-> ->].
    set (bs := file_read data off (Z_to_bv 64 count)).
    pose proof (length_file_read_le_count data off count Hc) as Hl. fold bs in Hl.
    exists (RdData bs). split.
    + unfold dec_read. destruct bs as [|b bs'] eqn:Ebs; cbn [delivered_writes].
      * unfold len_word. cbn [length Z.of_nat]. rewrite errno_of_lit by lia. reflexivity.
      * rewrite bv_eqb_refl. unfold len_word. rewrite unsigned_lit by (cbn [length] in *; lia).
        rewrite Z.eqb_refl.
        replace (1 <=? Z.of_nat (length (b :: bs')))%Z with true by (symmetry; apply Z.leb_le; cbn; lia).
        replace (Z.of_nat (length (b :: bs')) <=? count)%Z with true by (symmetry; apply Z.leb_le; lia).
        reflexivity.
    + exists p, off, data. auto.
  - destruct H as [-> ->]. exists (RdErr EISDIR). split; [reflexivity| auto].
  - destruct H as [-> ->]. exists (RdErr EBADF). split; [reflexivity| auto].
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_write : forall fd bs mo rsp mo' evs,
  (Z.of_nat (length bs) < 2^64)%Z ->
  nstep (NWrite fd bs) mo rsp mo' evs ->
  exists k, dec_write (Z.of_nat (length bs)) rsp = Some k /\ (1 <= k <= Z.of_nat (length bs))%Z
    /\ mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) bs).
Proof.
  intros fd bs mo rsp mo' evs Hl (k & Hk & -> & -> & ->). exists k. split; [|auto].
  unfold dec_write, dec_count, eff0. rewrite unsigned_lit by lia.
  replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia).
  replace (k <=? Z.of_nat (length bs))%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_writev : forall fd bufs mo rsp mo' evs,
  (Z.of_nat (length (concat bufs)) < 2^64)%Z ->
  nstep (NWritev fd bufs) mo rsp mo' evs ->
  exists k, dec_writev (Z.of_nat (length (concat bufs))) rsp = Some k
    /\ ((length (concat bufs) = 0%nat /\ k = 0) \/ (1 <= k <= Z.of_nat (length (concat bufs))))%Z
    /\ mo' = mo /\ evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) (concat bufs)).
Proof.
  intros fd bufs mo rsp mo' evs Hl [-> H]. cbv zeta in H. unfold dec_writev.
  destruct (Z.eqb_spec (Z.of_nat (length (concat bufs))) 0) as [E|E].
  - destruct H as [-> ->]. exists 0%Z. unfold dec_count0, eff0. rewrite unsigned_lit by lia. cbn.
    repeat split; auto. left. lia.
  - destruct H as (k & Hk & -> & ->). exists k. split; [| split; [right; lia| auto]].
    unfold dec_count, eff0. rewrite unsigned_lit by lia.
    replace (1 <=? k)%Z with true by (symmetry; apply Z.leb_le; lia).
    replace (k <=? Z.of_nat (length (concat bufs)))%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof. intros e H. cbn in H. unfold ENOMEM, EACCES, EMFILE, ENFILE in H. lia. Qed.

Lemma nstep_dec_open : forall path mo rsp mo' evs,
  minv mo ->
  nstep (NOpen path) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_open rsp = Some a /\
  match a with
  | SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
  | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z
      /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
      /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0))
         /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo
  end.
Proof.
  intros path mo rsp mo' evs Hminv [-> H]. split; [reflexivity|].
  assert (Herr : forall e, (1 <= e <= 4095)%Z -> rsp = efferr e -> mo' = mo ->
            exists a, dec_open rsp = Some a /\
            match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
            | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
  { intros e He -> ->. exists (SErr e). split; [apply (dec_plain_err _ []); exact He| auto]. }
  assert (Hres : forall ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) -> open_result mo ent rsp mo' ->
            exists a, dec_open rsp = Some a /\
            match a with SErr e => mo' = mo /\ (1 <= e <= 4095)%Z
            | SVal fd => Z_to_bv 64 fd = alloc_fd (m_fds mo) /\ (3 <= fd <= 4096)%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
                /\ exists ent, (ent = FdDir \/ ent = FdFile path (Z_to_bv 64 0)) /\ mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) ent) mo end).
  { intros ent Hent [(e & HIn & -> & ->) | (Hlk & -> & ->)].
    - apply (Herr e); [apply openat_errnos_range; exact HIn | reflexivity | reflexivity].
    - pose proof (alloc_fd_range mo Hminv Hlk) as Hr.
      exists (SVal (bv_unsigned (alloc_fd (m_fds mo)))). split.
      + unfold dec_open, eff0. rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
        apply (dec_plain_val _ []); [lia|]. apply andb_true_intro; split; apply Z.leb_le; lia.
      + rewrite Z_to_bv_bv_unsigned. split; [reflexivity|]. split; [lia|]. split; [exact Hlk|]. exists ent. auto. }
  destruct (path_max <=? length path)%nat. { destruct H as [-> ->]. apply (Herr ENAMETOOLONG); try reflexivity. unfold ENAMETOOLONG; lia. }
  destruct path as [|c path']. { destruct H as [-> ->]. apply (Herr ENOENT); try reflexivity. unfold ENOENT; lia. }
  destruct (path_is_dirref (c :: path')). { apply (Hres FdDir); [left; reflexivity| exact H]. }
  destruct (fs_lookup (m_fs mo) (c :: path')).
  - apply (Hres (FdFile (c :: path') (Z_to_bv 64 0))); [right; reflexivity| exact H].
  - destruct H as [-> ->]. apply (Herr ENOENT); try reflexivity. unfold ENOENT; lia.
Qed.

Lemma nstep_dec_close : forall fd mo rsp mo' evs,
  nstep (NClose fd) mo rsp mo' evs ->
  evs = [] /\
  exists a, dec_close rsp = Some a /\
  match a with
  | SErr e => e = EBADF /\ mo' = mo /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None
  | SVal v => v = 0%Z /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None
      /\ mo' = with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo
  end.
Proof.
  intros fd mo rsp mo' evs (-> & _ & H). split; [reflexivity|].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; destruct H as [-> ->].
  - exists (SVal 0). split; [apply (dec_plain_val _ []); [lia|reflexivity]|]. repeat split; congruence.
  - exists (SErr EBADF). split; [apply (dec_plain_err _ []); unfold EBADF; lia|]. auto.
Qed.

Lemma nstep_dec_ioctl : forall fd req mo rsp mo' evs,
  nstep (NIoctl fd req) mo rsp mo' evs ->
  dec_ioctl rsp = Some (SErr ENOTTY) /\ mo' = mo /\ evs = [].
Proof.
  intros fd req mo rsp mo' evs (-> & -> & ->). split; [|auto]. apply (dec_plain_err _ []). unfold ENOTTY; lia.
Qed.

Lemma nstep_dec_set_tid : forall mo rsp mo' evs,
  minv mo ->
  nstep NSetTid mo rsp mo' evs ->
  evs = [] /\
  exists t, dec_set_tid rsp = Some t /\ (0 < t < PID_MAX_ENVELOPE)%Z /\
  ((m_tid mo = Some (Z_to_bv 64 t) /\ mo' = mo) \/ (m_tid mo = None /\ mo' = with_tid (Z_to_bv 64 t) mo)).
Proof.
  intros mo rsp mo' evs Hminv (-> & tw & -> & H). split; [reflexivity|].
  exists (bv_unsigned tw). rewrite Z_to_bv_bv_unsigned.
  assert (Hr : (0 < bv_unsigned tw < PID_MAX_ENVELOPE)%Z).
  { destruct (m_tid mo) as [t0|] eqn:E.
    - destruct H as [-> _]. destruct Hminv as (_ & _ & _ & _ & _ & _ & MT & _). exact (MT _ E).
    - exact (proj1 H). }
  split.
  - unfold dec_set_tid, eff0. destruct Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. rewrite H1, H2. reflexivity.
  - split; [exact Hr|]. destruct (m_tid mo) as [t0|]; destruct H as [H0 ->]; [left; subst; auto| right; auto].
Qed.

Lemma nstep_exit_none : forall c mo rsp mo' evs, nstep (NExit c) mo rsp mo' evs -> False.
Proof. intros c mo rsp mo' evs H. exact H. Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk0 : forall mo rsp mo' evs,
  nstep (NBrk 0) mo rsp mo' evs ->
  evs = [] /\ dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo'
  /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo).
Proof.
  intros mo rsp mo' evs H.
  pose proof (nstep_mm_vm_only (NBrk 0) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|].
  apply nstep_brk_iff in H as [H _]. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 0) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  unfold brk_r_ok in E1. change (w_is0 (Z_to_bv 64 0)) with true in E1. cbn [orb] in E1. apply bv_eqb_eq in E1. subst r.
  apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3.
  unfold brk_zeros, brk_is_grow in E2. change (w_is0 (Z_to_bv 64 0)) with true in E2. cbn [negb andb] in E2. subst zs.
  unfold brk_unmaps, brk_page_range in E3. rewrite Z.ltb_irrefl in E3. destruct (0 <? _)%Z; subst us.
  all: inversion H; subst; split; [reflexivity|]; split; [exact Hv|].
  all: unfold with_brk_next, m_vmmaps; cbn; unfold brk_unmaps, brk_page_range; rewrite Z.ltb_irrefl; destruct (0 <? _)%Z; reflexivity.
Qed.

Lemma page_round_up_Z_mono : forall a b, (a <= b)%Z -> (page_round_up_Z a <= page_round_up_Z b)%Z.
Proof.
  intros a b H. unfold page_round_up_Z, page_size. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.

Lemma m_vmmaps_forget_vm_ranges : forall l m, m_vmmaps (forget_vm_ranges l m) = m_vmmaps m.
Proof. induction l as [|[a n] l IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma vm_brk_with_brk_next : forall m req r, vm_brk (m_vmmaps (with_brk_next m req r)) = r.
Proof. intros. unfold with_brk_next. cbv zeta. rewrite m_vmmaps_forget_vm_ranges. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof.
  intros req mo rsp mo' evs h Hb Hsb Hreq H.
  pose proof (nstep_mm_vm_only (NBrk req) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_brk_iff in H as [H _]. destruct rsp as [r ws zs us cs ci]. unfold check_brk in H.
  destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
  destruct (brk_r_ok mo (Z_to_bv 64 req) r && listNN_eqb zs _ && listNN_eqb us _) eqn:E; [|discriminate].
  assert (Hmo' : mo' = with_brk_next mo (Z_to_bv 64 req) r) by (inversion H; reflexivity).
  clear H. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply listNN_eqb_eq in E2. apply listNN_eqb_eq in E3. subst zs us.
  fold h in E1 |- *.
  unfold brk_r_ok in E1. rewrite w_is0_lit in E1 by lia.
  replace (req =? 0)%Z with false in E1 by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in E1. fold h in E1. rewrite unsigned_lit in E1 by lia.
  replace (req <? bv_unsigned (vm_start_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  replace (req <? bv_unsigned (vm_brk h))%Z with false in E1 by (symmetry; apply Z.ltb_ge; lia).
  cbn [orb] in E1. apply andb_prop in E1 as [E1 _].
  assert (Hr : r = Z_to_bv 64 req \/ r = vm_brk h).
  { apply orb_prop in E1 as [E1|E1]; apply bv_eqb_eq in E1; auto. }
  assert (Hus : brk_unmaps r (vm_brk h) = []).
  { unfold brk_unmaps, brk_page_range.
    assert (Hle : (page_round_up_Z (bv_unsigned (vm_brk h)) <= page_round_up_Z (bv_unsigned r))%Z).
    { apply page_round_up_Z_mono. destruct Hr as [-> | ->]; [rewrite unsigned_lit by lia|]; lia. }
    replace (page_round_up_Z (bv_unsigned r) <? page_round_up_Z (bv_unsigned (vm_brk h)))%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    destruct (0 <? _)%Z; reflexivity. }
  rewrite Hus.
  destruct (Z.eq_dec req (bv_unsigned (vm_brk h))) as [Ereq | Hne].
  -
    assert (Hr' : r = vm_brk h). { destruct Hr as [-> | ->]; [subst req; apply Z_to_bv_bv_unsigned| reflexivity]. }
    subst r. exists BrkSame. split; [|rewrite Hmo'; apply vm_brk_with_brk_next].
    unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
  - destruct Hr as [-> | ->].
    + exists BrkGrown. split; [|rewrite Hmo'; apply vm_brk_with_brk_next].
      unfold dec_brk. rewrite unsigned_lit by lia.
      replace (req =? bv_unsigned (vm_brk h))%Z with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [andb]. rewrite Z.eqb_refl.
      unfold brk_zeros, brk_is_grow. rewrite w_is0_lit by lia.
      replace (req =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (0 <? bv_unsigned (vm_brk h))%Z with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite unsigned_lit by lia.
      replace (bv_unsigned (vm_brk h) <? req)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      cbn [negb andb]. unfold brk_page_range, brk_new_pages, zeros_of, wa.
      destruct (_ <? _)%Z; rewrite (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity.
    + exists BrkSame. split; [|rewrite Hmo'; apply vm_brk_with_brk_next].
      unfold dec_brk. rewrite Z.eqb_refl. unfold brk_zeros, brk_is_grow. rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition covered (maps : list (word * word)) (iv : Z * Z) : Prop :=
  exists e sz, In (e, sz) maps /\ (bv_unsigned e <= fst iv)%Z /\ (snd iv <= bv_unsigned e + bv_unsigned sz)%Z.

Lemma region_free_In : forall maps a n e sz,
  region_free maps a n = true -> In (e, sz) maps ->
  (bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a)%Z.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n e sz H Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [|exact (IH _ _ _ _ H2 Hin)].
  inversion E; subst. unfold iv_overlap in H1.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e + bv_unsigned sz));
  destruct (Z.ltb_spec0 (bv_unsigned e) (bv_unsigned a + bv_unsigned n)); cbn in H1; try discriminate; lia.
Qed.

Lemma avoids_of_region_free : forall maps a n avoid,
  region_free maps a n = true ->
  Forall (covered maps) avoid ->
  avoids (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros maps a n avoid Hrf Hc. unfold avoids. apply forallb_forall. intros [lo hi] Hin.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (e & sz & He & H1 & H2). cbn in H1, H2. cbn [fst snd].
  pose proof (region_free_In _ _ _ _ _ Hrf He) as [H|H].
  - apply orb_true_intro. left. apply Z.leb_le. lia.
  - apply orb_true_intro. right. apply Z.leb_le. lia.
Qed.

(* [comment removed for export] *)
Ltac errno_enomem Herr :=
  let e := fresh "e" in let HIn := fresh "HIn" in
  apply errno_ret_in_true in Herr as (e & HIn & Herr);
  first [ destruct HIn as [<-|[]]
        | lazymatch type of HIn with
          | In _ (?f ?b) => unfold f in HIn; destruct b; [destruct HIn as [<-|[]] | destruct HIn]
          end ];
  try subst.

(* [comment removed for export] *)
Ltac case_errno_in_eqn H He :=
  match type of H with
  | context [errno_ret_in ?es ?r0] => destruct (errno_ret_in es r0) eqn:He
  end.

Lemma mmap_len_bound : forall len, (0 < len)%Z -> (len <= mmap_len len < len + 4096)%Z.
Proof. intros len H. unfold mmap_len, page_round_up_Z, page_size. split; [|]; nia || lia. Qed.

Lemma mmap_flags_plain : mmap_noreserve_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap : forall atop len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  (alloc_top h <= atop)%Z ->     (* [comment removed for export] *)
  nstep (NMmap 0 len (PROT_READ + PROT_WRITE) (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap atop len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok atop len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros atop len avoid mo rsp mo' evs h Hlen Hlen2 Hcov Htop H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H as (_ & H & _). destruct rsp as [r ws zs us cs ci]. unfold check_mmap, check_mmap_fixed_overflow in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H. cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE)) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. rewrite place_declined_b_null in H. cbv iota in H.
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  case_errno_in_eqn H Herr.
  - destruct zs; [|discriminate]. inversion H; subst.
    errno_enomem Herr.
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    unfold with_mmap_backing in H. rewrite mmap_flags_plain in H.
    inversion H; subst; clear H.
    (* LPS 727298f3: the grant test is [linux_place_is]; its admissible consequences are the
       four conditions the older checker listed. *)
    apply andb_prop in E as [E E6]. apply andb_prop in E as [EP E5].
    assert (HnA : (mmap_len len mod page_size = 0)%Z) by (unfold mmap_len, page_round_up_Z; apply Z_mod_mult).
    assert (HnP : (0 < mmap_len len)%Z) by (destruct Hb as [Hb1 _]; exact (Z.lt_le_trans _ _ _ Hlen Hb1)).
    destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_admissible _ _ _ _ _ HnP HnA EP) as (E1 & E2 & E3 & E4).
    apply listNN_eqb_eq in E6. subst zs.
    assert (Hok : mmap_addr_ok atop len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt _ _) E2).
      rewrite (proj2 (Z.leb_le _ atop)) by lia. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mmap_none : forall atop len avoid mo rsp mo' evs,
  let h := m_vmmaps mo in
  (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  Forall (covered (vm_reserved h ++ vm_maps h)) avoid ->
  (alloc_top h <= atop)%Z ->
  nstep (NMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANONYMOUS)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_none atop len avoid rsp = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok atop len avoid a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                                    ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h)
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros atop len avoid mo rsp mo' evs h Hlen Hlen2 Hcov Htop H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMmap 0 len _ _) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H as (_ & H & _). destruct rsp as [r ws zs us cs ci]. unfold check_mmap, check_mmap_fixed_overflow in H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.
  change (mmap_anon_b (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS))) with true in H. cbn [negb] in H.
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with false in H.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 (MAP_PRIVATE + MAP_ANONYMOUS)) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. rewrite place_declined_b_null in H. cbv iota in H.
  destruct ws; [|discriminate]. destruct zs; [|destruct us; discriminate].
  destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  fold h in H. rewrite unsigned_lit in H by lia. fold (mmap_len len) in H.
  case_errno_in_eqn H Herr.
  - destruct us; [|discriminate]. inversion H; subst.
    errno_enomem Herr.
    exists (MmErr ENOMEM). split; [|auto]. unfold dec_mmap_none. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:E; [|discriminate] end.
    unfold with_mmap_backing in H. rewrite mmap_flags_plain in H.
    inversion H; subst; clear H.
    apply andb_prop in E as [EP E5].
    assert (HnA : (mmap_len len mod page_size = 0)%Z) by (unfold mmap_len, page_round_up_Z; apply Z_mod_mult).
    assert (HnP : (0 < mmap_len len)%Z) by (destruct Hb as [Hb1 _]; exact (Z.lt_le_trans _ _ _ Hlen Hb1)).
    destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_admissible _ _ _ _ _ HnP HnA EP) as (E1 & E2 & E3 & E4).
    apply listNN_eqb_eq in E5. subst us.
    assert (Hok : mmap_addr_ok atop len avoid (bv_unsigned r) = true).
    { unfold mmap_addr_ok. rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt _ _) E2).
      rewrite (proj2 (Z.leb_le _ atop)) by lia. cbn [andb].
      rewrite <- (unsigned_lit (mmap_len len)) by lia. apply (avoids_of_region_free (vm_reserved h ++ vm_maps h)); [exact E4| exact Hcov]. }
    exists (MmOk (bv_unsigned r)). split.
    + unfold dec_mmap_none. rewrite !bv_eqb_refl, Hok. reflexivity.
    + rewrite Z_to_bv_bv_unsigned. split; [exact Hok|]. split; [exact E4|]. reflexivity.
Qed.

Lemma m_vmmaps_with_mmap_destroyed : forall a n h m, m_vmmaps (with_mmap_destroyed a n h m) = h.
Proof. reflexivity. Qed.

(* LPS 727298f3: munmap's next state is [mmap_fixed_destroyed_next], which subtracts the
   range from [vm_maps]; on a ledger where the range is exactly one entry and meets no
   other, that is [map_remove]. *)
Lemma iv_subtract_outside : forall (b s : word) lo hi,
  (0 < bv_unsigned s)%Z -> (lo < hi)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  iv_subtract b s lo hi = [(b, s)].
Proof.
  intros b s lo hi Hs Hlh Hd. unfold iv_subtract. cbv zeta.
  destruct Hd as [Hd|Hd].
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt hi (bv_unsigned b + bv_unsigned s))) by lia.
    rewrite Z.max_l by lia.
    replace (bv_unsigned b + bv_unsigned s - bv_unsigned b)%Z with (bv_unsigned s) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_exact : forall l (a n : word),
  (0 < bv_unsigned n)%Z ->
  (forall b s, In (b, s) l -> (0 < bv_unsigned s)%Z) ->
  (forall b s, In (b, s) l -> b = a -> s = n) ->
  (forall b s, In (b, s) l -> b <> a ->
     (bv_unsigned b + bv_unsigned s <= bv_unsigned a
      \/ bv_unsigned a + bv_unsigned n <= bv_unsigned b)%Z) ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = map_remove l a.
Proof.
  induction l as [|[b s] r IH]; intros a n Hn Hpos Hu Hd; [reflexivity|].
  assert (IHr : maps_subtract r (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = map_remove r a).
  { apply IH; [exact Hn
              | intros b' s' H; apply (Hpos b' s'); right; exact H
              | intros b' s' H; apply (Hu b' s'); right; exact H
              | intros b' s' H; apply (Hd b' s'); right; exact H]. }
  cbn [maps_subtract]. rewrite IHr.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove r a).
  destruct (bv_eqb b a) eqn:E; cbn [negb].
  - apply bv_eqb_eq in E. subst b.
    rewrite (Hu a s (or_introl eq_refl) eq_refl).
    unfold iv_subtract. cbv zeta.
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a))).
    rewrite (proj2 (Z.ltb_ge _ _) (Z.le_refl (bv_unsigned a + bv_unsigned n))).
    reflexivity.
  - assert (Hne : b <> a) by (intros ->; rewrite bv_eqb_refl in E; discriminate).
    rewrite (iv_subtract_outside b s); [reflexivity | | lia |].
    + exact (Hpos b s (or_introl eq_refl)).
    + exact (Hd b s (or_introl eq_refl) Hne).
Qed.

(* The exact arm's granted answer: the witness that a refusal of the same request is spurious. *)
Lemma check_munmap_exact_grant : forall (a len : word) mo nZ,
  page_round_up_Z (bv_unsigned len) = nZ ->
  (negb (bv_unsigned a mod page_size =? 0) || w_is0 len)%Z = false ->
  (TASK_SIZE <? bv_unsigned a + nZ)%Z = false ->
  map_has (vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true ->
  check_munmap a len (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 nZ)] [] []) mo
  = CheckOk (with_mmap_destroyed a (Z_to_bv 64 nZ) (mmap_fixed_destroyed_next (m_vmmaps mo) a (Z_to_bv 64 nZ)) mo) [].
Proof.
  intros a len mo nZ HnZ G1 G2 G3. unfold check_munmap. rewrite G1. cbv iota zeta.
  rewrite HnZ, G2, G3. cbv iota.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  replace (w_is0 (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  map_has (vm_maps h) a n = true ->
  maps_subtract (vm_maps h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = map_remove (vm_maps h) a ->
  nstep (NMunmap addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_munmap addr len rsp = Some x /\
  match x with
  | RgErr e => e = EINVAL /\ mo' = mo
  | RgDone false => mo' = mo /\ munmap_free_ok h a (mmap_len len) = true
  | RgDone true => map_has (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 Hhas0 Hex H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMunmap addr len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  pose proof H as Hst0.
  apply nstep_munmap_iff in H as [H _]. destruct rsp as [r ws zs us cs ci]. unfold check_munmap in H.
  fold a h in H.
rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z || w_is0 (Z_to_bv 64 len)) eqn:G1.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  cbv zeta in H. destruct (TASK_SIZE <? _)%Z eqn:G2.   (* [comment removed for export] *)
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_munmap. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  assert (HnZ : page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = mmap_len len).
  { rewrite (unsigned_lit len); [reflexivity|].
    split; [exact (Z.lt_le_incl _ _ Hlen) | exact (Z.le_lt_trans _ _ _ (proj1 Hb) Hlen2)]. }
  pose proof (nstep_munmap_nonrefusal _ _ _ _ _ _ _ _ _ Hst0
                (check_munmap_exact_grant a (Z_to_bv 64 len) mo (mmap_len len) HnZ G1 G2 Hhas0)
                ltac:(vm_compute; reflexivity)) as Hnr.
  cbn [eff_ret] in Hnr.
  rewrite Hhas0 in H. cbv iota in H.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
  cbv iota in H. rewrite Hnr in H. cbv iota in H.
  destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
  apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst us. unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
  exists (RgDone true). split; [|split; [exact Hhas0| rewrite m_vmmaps_with_mmap_destroyed; unfold mmap_fixed_destroyed_next; rewrite Hex; reflexivity]].
  unfold dec_munmap. subst a n. rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma nstep_dec_mprotect : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep (NMprotect addr len (PROT_READ + PROT_WRITE)) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => (e = EINVAL \/ e = ENOMEM) /\ mo' = mo
  | RgDone false => mo' = mo
  | RgDone true => map_contains (vm_noaccess h) a n = true /\ map_contains (vm_maps h) a n = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                                    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                                    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMprotect addr len _) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mprotect_iff in H as [H _]. destruct rsp as [r ws zs us cs ci]. unfold check_mprotect in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  change (mprotect_grows_conflict_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with false in H.
  change (mprotect_modeled_b (Z_to_bv 64 (PROT_READ + PROT_WRITE))) with true in H. cbn [negb] in H. cbv iota in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  destruct (two_pow_64 <=? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr ENOMEM). split; [|auto].
    unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
  cbv zeta in H. match type of H with context [negb (region_free (vdso_reserved ?k ?t) ?x ?y)] =>
    destruct (negb (region_free (vdso_reserved k t) x y)); [discriminate H|] end.
  destruct (map_contains (vm_noaccess h) a n && map_contains (vm_maps h) a n) eqn:Hc.
  - destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
    destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
    case_errno_in_eqn H Herr.
    + destruct zs; [|discriminate]. inversion H; subst.
      errno_enomem Herr.
      exists (RgErr ENOMEM). split; [|auto]. unfold dec_mprotect. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + destruct (mprotect_budget_ok mo a n && w_is0 r && listNN_eqb zs [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
      apply andb_prop in E as [E E2]. apply andb_prop in E as [_ E1]. apply listNN_eqb_eq in E2. subst zs.
      unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
      apply andb_prop in Hc as [Hc1 Hc2].
      exists (RgDone true). split; [| auto].
      unfold dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
  - destruct (map_contains (vm_maps h) a n && region_free (vm_noaccess h) a n); [|discriminate].
    destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (w_is0 r) eqn:E; [|discriminate]. inversion H; subst. unfold w_is0 in E. apply bv_eqb_eq in E. subst r.
    exists (RgDone false). split; [reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_madvise : forall addr len mo rsp mo' evs,
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  (0 <= addr < 2^64)%Z -> (0 < len)%Z -> (mmap_len len < 2^64)%Z ->
  nstep (NMadvise addr len) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_madvise addr len rsp = Some x /\
  match x with
  | RgErr e => e = EINVAL /\ mo' = mo
  | RgDone false => False
  | RgDone true => madvise_dontneed_ok h a n = true /\ mo' = madvise_dontneed_next mo a n
  end.
Proof.
  intros addr len mo rsp mo' evs h a n Ha Hlen Hlen2 H.
  pose proof (mmap_len_bound len Hlen) as Hb.
  pose proof (nstep_mm_vm_only (NMadvise addr len) mo rsp mo' evs I H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_madvise_iff in H. destruct rsp as [r ws zs us cs ci]. unfold check_madvise in H.
  fold a h in H. rewrite (unsigned_lit len) in H by lia. fold (mmap_len len) in H. fold n in H.
  change (negb (madvise_dontneed_b (Z_to_bv 64 4))) with false in H. cbv iota in H.
  destruct (negb (bv_unsigned a mod page_size =? 0)%Z).
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_madvise, dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  rewrite w_is0_lit in H by lia. replace (len =? 0)%Z with false in H by (symmetry; apply Z.eqb_neq; lia).
  destruct (two_pow_64 <=? _)%Z.
  { apply check_ret_only_ok_iff in H as (-> & -> & _). exists (RgErr EINVAL). split; [|auto].
    unfold dec_madvise, dec_mprotect. rewrite errno_of_errno_ret by (unfold EINVAL; lia). reflexivity. }
  cbv zeta in H.
  destruct (madvise_dontneed_ok h a n) eqn:Hok; [|discriminate].
  destruct ws; [|discriminate]. destruct us; [|destruct zs; discriminate].
  destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
  destruct (w_is0 r && listNN_eqb zs [(a, n)]) eqn:E; [|discriminate]. inversion H; subst; clear H.
  apply andb_prop in E as [E1 E2]. apply listNN_eqb_eq in E2. subst zs.
  unfold w_is0 in E1. apply bv_eqb_eq in E1. subst r.
  exists (RgDone true). split; [| auto].
  unfold dec_madvise, dec_mprotect. subst a n. rewrite !bv_eqb_refl. reflexivity.
Qed.
