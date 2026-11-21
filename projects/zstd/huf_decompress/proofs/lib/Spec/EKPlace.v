(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (43 recorded proofs replaced by written proofs (ARENA_top, ARENA_top_TASK_SIZE, cls_bounds and 40 more); nstep_munmap_intro restated for the revision's model; check_mmap_fixed_gate re-proved; nstep_mmap_ok_intro takes the premise that Linux's placement for the NULL hint gives its address (linux_place_is), the anonymous PROT_NONE check also tests the placement, and place_declined_b is false at the NULL hint (place_declined_b_null); check_mprotect_gate and nstep_mprotect_ok_intro take a range clear of the vDSO pair (zstd/zstd_frame_info's text); brk_r_ok_grant re-proved for the budget's brk_grow_bytes (zstd/simple_decompress's proof)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Cfg ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe STree Malloc KInv KStep PState KLink KEv Relim.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_EKPlace () := "C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib4Spec7EKPlace5ABASEC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib4Spec7EKPlace5ARENAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib5Nodes@alloc_ceiling_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesDalloc_ceiling_lo_valC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC59OSSVerify5KrLib3Lib5Nodes=TASK_SIZE_valC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec5KLink3ehiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink3eloC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace3eszC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z<log2_up_specC56Stdlib6ZArith6BinInt1Z7log2_upC56Stdlib6ZArith6BinInt1Z4predC56Stdlib6ZArith6BinInt1Z7sub_1_rC56Stdlib6ZArith6BinInt1Z?log2_up_le_monoC56Stdlib6ZArith6BinInt1Z<log2_up_pow2C56Stdlib6ZArith6BinInt1Z?log2_up_le_pow2C47Corelib4Init5Logic5proj1K47Corelib4Init5Logic3and01K46Stdlib9micromega6VarMap1t03c59OSSVerify5KrLib4Spec7EKPlace3clsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace3LIMC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z9pow_add_rK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib4Spec7EKPlace8zremove1C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z8inj_succI47Corelib4Init5Logic5False00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib5Lists4List6in_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib4Spec7EKPlace?zremove1_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib4Spec7EKPlace;zremove1_InC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes7nat_indI47Corelib4Init5Logic2ex00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith6BinInt1Z6eq_decC46Stdlib5Lists4List6filterC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z4succK46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib4Spec7EKPlace7in_corrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace:slab_entryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltc59OSSVerify5KrLib4Spec7EKPlace8ARENA_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace7ehi_eloC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z8lt_totalc59OSSVerify5KrLib4Spec7EKPlace:ARENA_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_lt_mono_pos_rc59OSSVerify5KrLib4Spec7EKPlace;pow35_splitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegc59OSSVerify5KrLib4Spec7EKPlace8in_arenaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace4CORRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace8ABASE_40C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace4NICEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5RelimAlive_bytes_nonnegC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace:cls_boundsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace8slot_idxC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List9filter_Inc59OSSVerify5KrLib4Spec7EKPlace=slab_in_arenaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib4Spec7EKPlace@live_bytes_lowerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlaceDlive_bytes_filter_leC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega5Tauto8GFormula01C46Stdlib5Lists4List:length_mapc59OSSVerify5KrLib4Spec7EKPlace6pigeonC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_mulC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega5Tauto8GFormula02K46Stdlib9micromega5Tauto8GFormula0:C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib4Init9Datatypes4bool02K46Stdlib9micromega5Tauto4kind02C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8map_consC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv:Z_mod_multI46Stdlib7Sorting;Permutation;Permutation00c59OSSVerify5KrLib4Spec7EKPlace?live_bytes_consC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_indC59OSSVerify5KrLib4Spec5KLink4vmwfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5KLink6pwdisj00C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec3KEv9pwdisj_InC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink5edisjC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5KLink6pwdisj02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5KLink6pwdisj01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K46Stdlib5Lists4List5NoDup01K46Stdlib5Lists4List5NoDup02C46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;Permutation>Permutation_inc59OSSVerify5KrLib4Spec7EKPlace:vmwf_nodupC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupc59OSSVerify5KrLib4Spec7EKPlace9vmwf_inclC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9in_or_appC46Stdlib5Lists4ListBNoDup_app_remove_rC46Stdlib5Lists4ListBNoDup_app_remove_lc59OSSVerify5KrLib4Spec7EKPlace9vmwf_tailC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes4negbC46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC46Stdlib5Lists4ListAforallb_filter_idC59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3minC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z8min_specC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractI47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC59OSSVerify5KrLib4Spec3KEvDiv_subtract_disjointC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC46Stdlib5Lists4List>existsb_existsc59OSSVerify5KrLib4Spec7EKPlaceImaps_subtract_disjoint_idC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlaceIlive_bytes_iv_subtract_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Relim>live_bytes_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List8flat_mapC46Stdlib7Sorting;PermutationDPermutation_flat_mapc59OSSVerify5KrLib4Spec7EKPlaceFmaps_subtract_flat_mapC1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation01K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool<andb_false_rC59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib4Spec5Relim?backing_le_liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedI4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC59OSSVerify5KrLib3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State:fdst_tableC4ELinuxProcessSemantics?LinuxProcessSem5State:fsst_imageI4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00C6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude:listNN_eqbC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude=listNN_eqb_eqC4ELinuxProcessSemantics?LinuxProcessSem5State8in_sysnoC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<errno_ret_inC4ELinuxProcessSemantics?LinuxProcessSem3Run=ret_in_errnosC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bC59OSSVerify5KrLib3Lib3Cfg=refusal_b_222C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunLspurious_refusal_not_refusalI4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;mmap_errnosC59OSSVerify5KrLib3Lib3Cfg4ACFGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Cfg=refusal_b_226C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8Mprotect?mprotect_errnosC4ELinuxProcessSemantics?LinuxProcessSem3Run=brk_refusal_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap8brk_r_okK59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap9check_brkK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result01C59OSSVerify5KrLib3Lib5Nodes:pure_inputC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunDspurious_refusal_cfgC59OSSVerify5KrLib3Lib5Nodes=nstep_brk_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap9brk_zerosC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap:brk_unmapsK4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap=with_brk_nextc59OSSVerify5KrLib4Spec7EKPlace?listNN_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6in_argC59OSSVerify5KrLib3Lib3Cfg=refusal_b_214C1?~~~~~~~~~~~~~~~I6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00K6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result02C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap7min_brkC47Corelib4Init9Datatypes3orbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap;brk_grow_okC46Stdlib4Bool4Bool:orb_true_rC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC45stdpp9bitvector;definitions6bv_subC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC56Stdlib6ZArith6BinInt1Z:ltb_irreflC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions?bv_sub_unsignedC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib3Lib5Nodes9w_is0_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C59OSSVerify5KrLib4Spec5KStep<page_size_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KStep;mmap_len_geC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap:check_mmapC59OSSVerify5KrLib3Lib5Nodes>nstep_mmap_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeAerrno_ret_in_trueC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7PreludeBerrno_ret_unsignedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAmmap_plain_anon_bC6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude>check_ret_onlyC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapHmmap_noreserve_backed_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_fixed_destroyed_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCwith_mmap_destroyedC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapMmmap_fixed_noaccess_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapLmmap_fixed_rw_span_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapImmap_noreplace_noaccess_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapCmmap_noreplace_rw_bC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapAwith_mmap_backingC59OSSVerify5KrLib4Spec5RelimGwith_mmap_backing_plainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC59OSSVerify5KrLib4Spec5RelimNmmap_noreserve_backed_ok_plainC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_pglen_ok_bc59OSSVerify5KrLib4Spec7EKPlaceHmmap_success_nonspuriousC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEwith_mmap_replacementC59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMC4ELinuxProcessSemantics?LinuxProcessSem5State6EINVALK6ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys7Prelude<check_result03C4ELinuxProcessSemantics?LinuxProcessSem5State6EEXISTC59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace<fixed_done_hC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlaceEcheck_mmap_fixed_gateC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateDm_vmmaps_with_vmmapsC59OSSVerify5KrLib4Spec5RelimHm_vmmaps_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5RelimKwith_mmap_replacement_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesCvm_only_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesGvm_only_replacement_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=vm_only_transC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasK59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm4Mmap<check_munmapC59OSSVerify5KrLib3Lib5Nodes@nstep_munmap_iffC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlace8munmap_hC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC59OSSVerify5KrLib3Lib6DecodeLm_vmmaps_with_mmap_destroyedC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectBmprotect_budget_okC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC7ELinuxProcessSemantics?LinuxProcessSem6Checks3Sys2Mm8Mprotect>check_mprotectC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesK59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5NodesBnstep_mprotect_iffC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5RelimEm_vm_lazy_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5RelimMm_vm_materialized_with_vmmapsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_transc59OSSVerify5KrLib4Spec7EKPlaceCcheck_mprotect_gateC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7EKPlaceLmprotect_success_nonspuriousC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LIM : Z := 2^34.            (* [comment removed for export] *)
Definition CORR : Z := 2^35.           (* [comment removed for export] *)
Definition ABASE : Z := 3 * 2^44.      (* [comment removed for export] *)
Definition ARENA (c : Z) : Z := ABASE + (c - 12) * 2^35.
Definition cls (n : Z) : Z := Z.log2_up n.
Definition esz (e : word * word) : Z := bv_unsigned (snd e).

Lemma ABASE_40 : 2^40 <= ABASE.
Proof.
ltac2:(KReplay.run1 (kr_t_EKPlace ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;3p;4p;7p-1p10000p4p710p8p1000Gp4p710p1000dp4p710p8g001Bj1FTg001bj1ETg002Bj1;Tg002`j18Tg003>j1DTg003ij10Tg004Nj11Tg004lj24Tg005Oj12Tg0064j13Tg006Rj35Tg0075j39Tg007Xj4:Tg008Cj7CTg008gj2BTg009Ij2@Tg009cj2=Tg00:Oj3>Tg00:ij3?Tg00;Hj4<Tg00<:j26Tg00<Wj2ATg00=4j27Tg00=PR0#F%E0g00><R0#;%80%D0R1g00>Zg00?9R2P2g00?YR2P0g00@9R3#0R4#1R5,40R6%24R4#0#0#0R7#3550g00@^%23#1R3,40%24#0#0R4#39506590C:g00AEFC1B12f0R2f2R1g00AeR6g00BER8'@1=21=>68dg00Bef15?0C<b1b2b3%17,65R7%14,65,A3'7P2b0g00CC,77eo"). Qed.
(* [comment removed for export] *)
Lemma ARENA_top : ARENA 34 + 2^35 <= alloc_ceiling_lo.
Proof. rewrite alloc_ceiling_lo_val. unfold ARENA, ABASE. lia. Qed.
Lemma ARENA_top_TASK_SIZE : ARENA 34 + 2^35 <= TASK_SIZE.
Proof. rewrite TASK_SIZE_val. unfold ARENA, ABASE. lia. Qed.

Definition slab_entry (e : word * word) : Prop :=
  exists c i, 12 <= c <= 34 /\ 0 <= i < 2^(35 - c) /\ elo e = ARENA c + i * 2^c /\ 2^(c-1) < esz e <= 2^c.
Definition in_corr (b0 : Z) (e : word * word) : Prop := b0 <= elo e /\ ehi e <= b0 + CORR.
Definition NICE (b0 : Z) (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> in_corr b0 e \/ slab_entry e) /\ 0 < b0 /\ b0 + CORR <= 2^40.

Lemma ehi_elo : forall e, ehi e = elo e + esz e.
Proof.
ltac2:(KReplay.run1 (kr_t_EKPlace ()) [] "p'0h01ah11eh21ni001bi011pp;1p;2p;3p;4g003ij10Tg0064j1:Tg00MWj15Tg00N:R0j24Tg00NZj19Tg00OMj13Tg00P@j12Tg00Gaj21Tg00:Oj36Tg00Q5j47Tg009Ij28Tg00@9#0#0#0#0#0#0#:#5R1/41P0P1P1g00><R0f0R2#9%32%22'136P2P1P1f1R3P2C7R4#3%24'1,80X21X01P3P2O2n2001101000120100100W1o"). Qed.

Lemma cls_bounds : forall n, PGSZ <= n <= LIM -> 12 <= cls n <= 34 /\ 2^(cls n - 1) < n <= 2^(cls n).
Proof.
  intros n Hn. unfold cls, PGSZ, LIM in *.
  pose proof (Z.log2_up_spec n ltac:(lia)) as [H1 H2]. rewrite <- Z.sub_1_r in H1.
  split; [|lia]. split.
  - pose proof (Z.log2_up_le_mono (2^12) n ltac:(lia)) as H. rewrite Z.log2_up_pow2 in H by lia. lia.
  - apply (proj1 (Z.log2_up_le_pow2 n 34 ltac:(lia))). lia.
Qed.

Lemma pow35_split : forall c, 0 <= c <= 35 -> 2^35 = 2^(35-c) * 2^c.
Proof. intros c Hc. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma ARENA_mono : forall c c', c < c' -> ARENA c + 2^35 <= ARENA c'.
Proof. intros. unfold ARENA. nia. Qed.

Lemma ARENA_lo : forall c, 12 <= c -> ABASE <= ARENA c.
Proof. intros. unfold ARENA. nia. Qed.

(* [comment removed for export] *)
Fixpoint zremove1 (x : Z) (l : list Z) : list Z :=
  match l with [] => [] | y :: l' => if y =? x then l' else y :: zremove1 x l' end.
Lemma zremove1_length : forall x l, In x l -> length (zremove1 x l) = (length l - 1)%nat.
Proof.
  induction l as [|y l IH]; intros Hin; [destruct Hin|]. cbn. destruct (Z.eqb_spec y x); [cbn; lia|].
  destruct Hin as [->|Hin]; [contradiction|]. cbn. rewrite IH by exact Hin. destruct l; [destruct Hin| cbn; lia].
Qed.
Lemma zremove1_In : forall x z l, In z l -> z <> x -> In z (zremove1 x l).
Proof.
  induction l as [|y l IH]; intros Hin Hne; [destruct Hin|]. cbn. destruct (Z.eqb_spec y x).
  - destruct Hin as [->|Hin]; [contradiction| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.
Lemma pigeon : forall N (l : list Z), (length l < N)%nat -> exists i, 0 <= i < Z.of_nat N /\ ~ In i l.
Proof.
  induction N as [|N IH]; intros l Hl; [lia|].
  destruct (in_dec Z.eq_dec (Z.of_nat N) l) as [Hin|Hnin].
  - destruct (IH (zremove1 (Z.of_nat N) l)) as (i & Hi & Hni); [rewrite zremove1_length by exact Hin; destruct l; [destruct Hin| cbn [length] in *; lia]|].
    exists i. split; [lia|]. intros Hin'. apply Hni. apply zremove1_In; [exact Hin'| lia].
  - exists (Z.of_nat N). split; [lia| exact Hnin].
Qed.

(* [comment removed for export] *)
Lemma live_bytes_filter_le : forall f l, live_bytes (List.filter f l) <= live_bytes l.
Proof.
  induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). destruct (f (a, n)); cbn; lia.
Qed.
Lemma live_bytes_lower : forall l m, (forall e, In e l -> m < esz e) -> Z.of_nat (length l) * m <= live_bytes l - Z.of_nat (length l).
Proof.
  induction l as [|[a n] l IH]; intros m H; cbn -[Z.of_nat]; [lia|].
  specialize (IH m (fun e He => H e (or_intror He))). pose proof (H (a, n) (or_introl eq_refl)) as Hn. unfold esz in Hn; cbn in Hn.
  rewrite Nat2Z.inj_succ. nia.
Qed.

Definition in_arena (c : Z) (e : word * word) : bool := (ARENA c <=? elo e) && (elo e <? ARENA c + 2^35).
Definition slot_idx (c : Z) (e : word * word) : Z := (elo e - ARENA c) / 2^c.

Lemma slab_in_arena : forall b0 e c, 0 < b0 -> b0 + CORR <= 2^40 -> 12 <= c <= 34 -> elo e < ehi e ->
  in_corr b0 e \/ slab_entry e -> in_arena c e = true ->
  exists i, 0 <= i < 2^(35-c) /\ elo e = ARENA c + i * 2^c /\ 2^(c-1) < esz e <= 2^c.
Proof.
  intros b0 e c Hb0 Hc0 Hc Hpos [Hcor|(c' & i & Hc' & Hi & He & Hsz)] Ha; unfold in_arena in Ha; apply andb_prop in Ha as [A1 A2]; apply Z.leb_le in A1; apply Z.ltb_lt in A2.
  - exfalso. destruct Hcor as [C1 C2]. pose proof (ARENA_lo c ltac:(lia)). pose proof ABASE_40. unfold CORR in *. pose proof (ehi_elo e). pose proof (bv_unsigned_in_range 64 (snd e)). unfold esz in *. nia.
  - assert (c' = c).
    { destruct (Z.lt_total c' c) as [Hlt|[Heq|Hgt]]; [| exact Heq |]; exfalso.
      + pose proof (ARENA_mono c' c Hlt). assert (i * 2^c' < 2^35); [|lia].
        rewrite (pow35_split c') by lia. apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg|]; lia.
      + pose proof (ARENA_mono c c' Hgt). assert (0 <= i * 2^c') by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]). lia. }
    subst c'. exists i. auto.
Qed.

Lemma free_slot : forall b0 maps n,
  NICE b0 maps -> (forall e, In e maps -> elo e < ehi e) -> live_bytes maps + n <= LIM -> PGSZ <= n ->
  let c := cls n in
  exists i, 0 <= i < 2^(35 - c) /\
    forall e, In e maps -> ehi e <= ARENA c + i * 2^c \/ ARENA c + i * 2^c + n <= elo e.
Proof.
  intros b0 maps n (Hn1 & Hb0 & Hc40) Hwf Hlive Hpg c.
  pose proof (live_bytes_nonneg maps) as Hnn.
  pose proof (cls_bounds n ltac:(unfold LIM in *; lia)) as [Hc Hsz]. fold c in Hc, Hsz.
  set (E := List.filter (in_arena c) maps).
  set (idx := map (slot_idx c) E).
  assert (HE : forall e, In e E -> exists i, 0 <= i < 2^(35-c) /\ elo e = ARENA c + i * 2^c /\ 2^(c-1) < esz e <= 2^c).
  { intros e He. apply filter_In in He as [He Ha]. eapply (slab_in_arena b0); eauto. }
  assert (Hlen : (length idx < Z.to_nat (2^(35-c)))%nat).
  { unfold idx. rewrite length_map.
    pose proof (live_bytes_lower E (2^(c-1)) ltac:(intros e He; destruct (HE e He) as (i & _ & _ & H); lia)) as HL.
    pose proof (live_bytes_filter_le (in_arena c) maps) as HF. fold E in HF.
    assert (Hp : 2^34 = 2^(35-c) * 2^(c-1)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    assert (0 < 2^(c-1)) by (apply Z.pow_pos_nonneg; lia). assert (0 < 2^(35-c)) by (apply Z.pow_pos_nonneg; lia).
    unfold LIM in Hlive. nia. }
  destruct (pigeon (Z.to_nat (2^(35-c))) idx Hlen) as (i & Hi & Hni). rewrite Z2Nat.id in Hi by (apply Z.pow_nonneg; lia).
  exists i. split; [exact Hi|]. intros e He.
  assert (Hpc : 0 < 2^c) by (apply Z.pow_pos_nonneg; lia).
  assert (Hslot : ARENA c + i * 2^c + n <= ARENA c + 2^35).
  { assert (i * 2^c + 2^c <= 2^35); [|lia]. rewrite (pow35_split c) by lia. nia. }
  destruct (in_arena c e) eqn:Ha.
  - destruct (HE e ltac:(apply filter_In; auto)) as (j & Hj & Hej & Hszj).
    assert (Hji : j <> i).
    { intros ->. apply Hni. unfold idx. apply in_map_iff. exists e. split; [|apply filter_In; auto].
      unfold slot_idx. rewrite Hej. replace (ARENA c + i * 2^c - ARENA c) with (i * 2^c) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite ehi_elo, Hej. destruct (Z.lt_total j i) as [Hlt|[Heq|Hgt]]; [left| contradiction| right]; nia.
  - unfold in_arena in Ha. destruct (Hn1 e He) as [[C1 C2]|(c' & j & Hc' & Hj & Hej & Hszj)].
    + left. pose proof (ARENA_lo c ltac:(lia)). pose proof ABASE_40. unfold CORR in *. nia.
    + assert (c' <> c).
      { intros ->. apply Bool.andb_false_iff in Ha. destruct Ha as [Ha|Ha]; [apply Z.leb_gt in Ha| apply Z.ltb_ge in Ha]; [nia|].
        assert (j * 2^c < 2^35); [|lia]. rewrite (pow35_split c) by lia. apply Z.mul_lt_mono_pos_r; lia. }
      rewrite ehi_elo, Hej. destruct (Z.lt_total c' c) as [Hlt|[Heq|Hgt]]; [left| contradiction| right].
      * pose proof (ARENA_mono c' c Hlt). assert (j * 2^c' + 2^c' <= 2^35); [|lia].
        rewrite (pow35_split c') by lia. assert (0 < 2^c') by (apply Z.pow_pos_nonneg; lia). nia.
      * pose proof (ARENA_mono c c' Hgt). assert (0 <= j * 2^c') by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]). lia.
Qed.

Lemma slab_entry_lo : forall e, slab_entry e -> 2^40 <= elo e.
Proof.
  intros e (c & i & Hc & Hi & He & _). rewrite He. pose proof (ARENA_lo c ltac:(lia)). pose proof ABASE_40.
  assert (0 <= i * 2^c) by (apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]). lia.
Qed.

Lemma ARENA_aligned : forall c i, 12 <= c -> 0 <= i -> (ARENA c + i * 2^c) mod 4096 = 0.
Proof.
  intros c i Hc Hi. unfold ARENA, ABASE.
  assert (E : 2^c = 2^(c-12) * 4096). { change 4096 with (2^12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite E. replace (3 * 2^44 + (c - 12) * 2 ^ 35 + i * (2 ^ (c - 12) * 4096)) with ((3 * 2^32 + (c - 12) * 2^23 + i * 2^(c-12)) * 4096) by lia.
  apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_cons : forall e l, live_bytes (e :: l) = esz e + live_bytes l.
Proof. intros [a n] l. reflexivity. Qed.

Lemma live_bytes_perm : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof.
  intros l l' HP. induction HP; [reflexivity| | |lia].
  - rewrite !live_bytes_cons. lia.
  - rewrite !live_bytes_cons. lia.
Qed.

Lemma vmwf_incl : forall l l', vmwf l -> (forall e, In e l' -> In e l) -> List.NoDup l' -> vmwf l'.
Proof.
  intros l l' [Hb Hp] Hi Hnd. split; [intros e He; apply Hb; auto|].
  induction l' as [|e l' IH]; [constructor|]. inversion Hnd; subst. constructor.
  - intros e' He'. destruct (pwdisj_In l e e' Hp (Hi e (or_introl eq_refl)) (Hi e' (or_intror He'))) as [->|D]; [contradiction| exact D].
  - apply IH; [intros x Hx; apply Hi; right; exact Hx| assumption].
Qed.

Lemma vmwf_nodup : forall l, vmwf l -> List.NoDup l.
Proof.
  intros l [Hb Hp]. induction l as [|e l IH]; [constructor|]. inversion Hp; subst. constructor.
  - intros Hin. pose proof (H1 e Hin) as D. pose proof (Hb e (or_introl eq_refl)). unfold edisj in D. lia.
  - apply IH; [intros x Hx; apply Hb; right; exact Hx| assumption].
Qed.

Lemma vmwf_perm : forall l l', Permutation l l' -> vmwf l -> vmwf l'.
Proof.
  intros l l' HP Hw. eapply vmwf_incl; [exact Hw| intros e He; eapply Permutation_in; [apply Permutation_sym; exact HP| exact He]|].
  eapply Permutation_NoDup; [exact HP| apply vmwf_nodup; exact Hw].
Qed.

Lemma vmwf_tail : forall e l, vmwf (e :: l) -> vmwf l.
Proof. intros e l [Hb Hp]. inversion Hp; subst. split; [intros x Hx; apply Hb; right; exact Hx| assumption]. Qed.

Lemma vmwf_app_l : forall l1 l2, vmwf (l1 ++ l2) -> vmwf l1.
Proof.
  intros l1 l2 Hw. eapply vmwf_incl; [exact Hw| intros e He; apply in_or_app; left; exact He|].
  apply vmwf_nodup in Hw. apply List.NoDup_app_remove_r in Hw. exact Hw.
Qed.
Lemma vmwf_app_r : forall l1 l2, vmwf (l1 ++ l2) -> vmwf l2.
Proof.
  intros l1 l2 Hw. eapply vmwf_incl; [exact Hw| intros e He; apply in_or_app; right; exact He|].
  apply vmwf_nodup in Hw. apply List.NoDup_app_remove_l in Hw. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_remove : forall maps a n, vmwf maps -> In (a, n) maps ->
  live_bytes (map_remove maps a) = live_bytes maps - bv_unsigned n.
Proof.
  induction maps as [|[a0 n0] maps IH]; intros a n Hw Hin; [destruct Hin|].
  pose proof (vmwf_tail _ _ Hw) as Hw'. destruct Hw as [Hb Hp]. inversion Hp; subst.
  unfold map_remove. cbn [List.filter fst]. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite bv_eqb_refl. cbn [negb]. rewrite live_bytes_cons. unfold esz; cbn [snd].
    enough (List.filter (fun p : word * word => negb (bv_eqb (fst p) a)) maps = maps) as -> by lia.
    apply List.forallb_filter_id. apply forallb_forall. intros [a' n'] Hin'. cbn [fst].
    destruct (bv_eqb a' a) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst a'. exfalso.
    pose proof (H1 _ Hin') as D. pose proof (Hb (a, n) (or_introl eq_refl)). pose proof (Hb (a, n') (or_intror Hin')). unfold edisj, elo, ehi in *. cbn in *. lia.
  - destruct (bv_eqb a0 a) eqn:E.
    + apply bv_eqb_eq in E. subst a0. exfalso.
      pose proof (H1 _ Hin) as D. pose proof (Hb (a, n0) (or_introl eq_refl)). pose proof (Hb (a, n) (or_intror Hin)). unfold edisj, elo, ehi in *. cbn in *. lia.
    + cbn [negb]. rewrite !live_bytes_cons. fold (map_remove maps a). rewrite (IH a n Hw' Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_in : forall a sz lo hi,
  bv_unsigned a <= lo -> lo < hi -> hi <= bv_unsigned a + bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  live_bytes (iv_subtract a sz lo hi) = bv_unsigned sz - (hi - lo).
Proof.
  intros a sz lo hi H1 H2 H3 H4. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn -[Z.min Z.max Z_to_bv bv_unsigned Z.sub Z.add];
    rewrite ?unsigned_lit by lia; lia.
Qed.

Lemma maps_subtract_disjoint_id : forall maps lo hi, vmwf maps -> lo < hi ->
  (forall e, In e maps -> ehi e <= lo \/ hi <= elo e) -> maps_subtract maps lo hi = maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hw Hlh Hd; [reflexivity|]. cbn.
  pose proof (proj1 Hw (a, sz) (or_introl eq_refl)) as W. unfold elo, ehi in W; cbn in W.
  rewrite iv_subtract_disjoint; [| lia| exact Hlh| specialize (Hd (a, sz) (or_introl eq_refl)); unfold elo, ehi in Hd; cbn in Hd; lia].
  cbn. f_equal. apply IH; [eapply vmwf_tail; exact Hw| exact Hlh| intros e He; apply Hd; right; exact He].
Qed.

Lemma live_bytes_subtract : forall maps lo n, vmwf maps -> 0 < bv_unsigned n -> bv_unsigned lo + bv_unsigned n <= 2^64 ->
  map_contains maps lo n = true ->
  live_bytes (maps_subtract maps (bv_unsigned lo) (bv_unsigned lo + bv_unsigned n)) = live_bytes maps - bv_unsigned n.
Proof.
  intros maps lo n Hw Hn Hb Hc.
  unfold map_contains in Hc. apply existsb_exists in Hc as ([a0 s0] & Hin & Hc). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. cbn [fst snd] in C1, C2.
  revert Hw Hin. induction maps as [|[a sz] maps IH]; intros Hw Hin; [destruct Hin|].
  pose proof (vmwf_tail _ _ Hw) as Hw'. destruct Hw as [Hbd Hp]. inversion Hp; subst. cbn [maps_subtract]. rewrite live_bytes_app, !live_bytes_cons. unfold esz; cbn [snd].
  destruct Hin as [E|Hin].
  - injection E as -> ->. pose proof (Hbd (a0, s0) (or_introl eq_refl)) as W. unfold elo, ehi in W; cbn in W.
    rewrite live_bytes_iv_subtract_in by lia.
    rewrite maps_subtract_disjoint_id; [lia| exact Hw'| lia|].
    intros e He. pose proof (H1 e He) as D. unfold edisj, elo, ehi in D |- *. cbn in D. lia.
  - pose proof (H1 _ Hin) as D. pose proof (Hbd (a, sz) (or_introl eq_refl)) as W. unfold edisj, elo, ehi in D, W; cbn in D, W.
    rewrite iv_subtract_disjoint; [| lia| lia| lia]. rewrite live_bytes_cons. unfold esz; cbn [snd].
    rewrite (IH Hw' Hin). cbn [live_bytes]. lia.
Qed.

Lemma maps_subtract_app : forall l1 l2 lo hi, maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a n] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma maps_subtract_flat_map : forall l lo hi, maps_subtract l lo hi = flat_map (fun e => iv_subtract (fst e) (snd e) lo hi) l.
Proof. induction l as [|[a n] l IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma maps_subtract_perm : forall l l' lo hi, Permutation l l' -> Permutation (maps_subtract l lo hi) (maps_subtract l' lo hi).
Proof. intros. rewrite !maps_subtract_flat_map. apply Permutation_flat_map. assumption. Qed.

Lemma live_bytes_ge_elem : forall e l, In e l -> esz e <= live_bytes l.
Proof.
  induction l as [|e' l IH]; intros Hin; [destruct Hin|]. rewrite live_bytes_cons. pose proof (live_bytes_nonneg l).
  destruct Hin as [<-|Hin]; [lia|]. specialize (IH Hin). pose proof (bv_unsigned_in_range 64 (snd e')). unfold esz in *. lia.
Qed.

Lemma Permutation_filter {A} : forall (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros f l l' HP. induction HP; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma filter_id {A} : forall (f : A -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  induction l as [|x l IH]; intros H; cbn; [reflexivity|]. rewrite (H x (or_introl eq_refl)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma region_free_intro : forall maps aw nw,
  (forall e, In e maps -> ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold elo, ehi in H; cbn in H.
  destruct H as [H|H].
  - replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - replace (bv_unsigned e <? bv_unsigned aw + bv_unsigned nw) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma backing_le_live_minv : forall mo, minv mo -> vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof. intros mo Hmi. apply backing_le_live; apply Hmi. Qed.

Lemma vm_only_tables : forall m m', vm_only m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' (F & _ & S & _). unfold m_fds, m_fs. rewrite F, S. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma listNN_eqb_refl : forall l, listNN_eqb l l = true.
Proof. intros l. apply listNN_eqb_eq. reflexivity. Qed.

Lemma mmap_success_nonspurious : forall i mo eff,
  bv_unsigned (in_sysno i) = 222 -> errno_ret_in mmap_errnos (eff_ret eff) = false ->
  ~ spurious_refusal_cfg ACFG i mo eff.
Proof. intros i mo eff E H. apply spurious_refusal_not_refusal. rewrite refusal_b_222 by exact E. exact H. Qed.

Lemma mprotect_success_nonspurious : forall i mo eff,
  bv_unsigned (in_sysno i) = 226 -> errno_ret_in mprotect_errnos (eff_ret eff) = false ->
  ~ spurious_refusal_cfg ACFG i mo eff.
Proof. intros i mo eff E H. apply spurious_refusal_not_refusal. rewrite refusal_b_226 by exact E. exact H. Qed.

Lemma brk_refusal_query : forall mo r, brk_refusal_b mo (Z_to_bv 64 0) r = false.
Proof. intros mo r. unfold brk_refusal_b. change (w_is0 (Z_to_bv 64 0)) with true. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_brk_intro : forall req mo r,
  let h := m_vmmaps mo in
  brk_r_ok mo (Z_to_bv 64 req) r = true ->
  brk_refusal_b mo (Z_to_bv 64 req) r = false ->
  nstep (NBrk req) mo (mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] [])
        (with_brk_next mo (Z_to_bv 64 req) r) [].
Proof.
  intros req mo r h Hr Hnr. apply nstep_brk_iff. split.
  - unfold check_brk. fold h. rewrite Hr, !listNN_eqb_refl. reflexivity.
  - apply spurious_refusal_not_refusal. rewrite refusal_b_214 by reflexivity. exact Hnr.
Qed.

Lemma brk_r_ok_refuse : forall mo req, brk_r_ok mo req (vm_brk (m_vmmaps mo)) = true.
Proof.
  intros mo req. unfold brk_r_ok.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps mo)))); [apply bv_eqb_refl|].
  destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps mo))); [rewrite bv_eqb_refl; apply orb_true_r|].
  rewrite bv_eqb_refl, orb_true_r. cbn [andb]. unfold brk_grow_ok, brk_budget_ok. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_r_ok_grant : forall mo req,
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  bv_unsigned (vm_start_brk h) <= b -> 0 < b -> b < req < 2^64 - 4096 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  req <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (vm_brk h) (Z_to_bv 64 (req + 4096 - b)) = true ->
  vm_backing_used mo + (req - b) <= vm_limit h ->
  brk_r_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true.
Proof.
  intros mo req h b Hs Hb Hreq Hba Hra Hc Hrf Hl. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
  unfold brk_r_ok. fold h. rewrite w_is0_lit by lia. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk. rewrite unsigned_lit by lia. replace (req <? bv_unsigned (vm_start_brk h)) with false by (symmetry; apply Z.ltb_ge; lia).
  fold b. replace (req <? b) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb]. rewrite bv_eqb_refl. cbn [orb andb].
  unfold brk_grow_ok, brk_budget_ok. fold h. rewrite unsigned_lit by lia. fold b.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia). replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  unfold page_round_up_Z. rewrite page_size_eq.
  replace ((b + 4096 - 1) / 4096 * 4096) with b.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia).
  rewrite (proj2 (Z.leb_le _ _) Hc). subst b. rewrite Z_to_bv_bv_unsigned, Hrf. cbn [andb].
  (* LPS 727298f3: the budget counts brk_grow_bytes, the pages between the page-rounded breaks *)
  unfold brk_grow_bytes. fold h. rewrite unsigned_lit by lia. unfold page_round_up_Z. rewrite page_size_eq.
  replace ((req + 4096 - 1) / 4096 * 4096) with req.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace ((bv_unsigned (vm_brk h) + 4096 - 1) / 4096 * 4096) with (bv_unsigned (vm_brk h)).
  2:{ pose proof (Z_div_mod_eq_full (bv_unsigned (vm_brk h)) 4096). pose proof (Z_div_mod_eq_full (bv_unsigned (vm_brk h)+4096-1) 4096).
      pose proof (Z.mod_pos_bound (bv_unsigned (vm_brk h)+4096-1) 4096). nia. }
  apply Z.leb_le. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_mmap_ok_intro : forall len prot mo a,
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  0 < a -> a mod 4096 = 0 -> a + n <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  vm_backing_used mo + n <= vm_limit h ->
  (* LPS 727298f3: a fresh grant takes the one address Linux gives; [a] is that address *)
  Placement.linux_place_is h (kb_thp (m_kernel mo)) (Z_to_bv 64 0) n (Z_to_bv 64 a) = true ->
  nstep (NMmap 0 len prot MAPF) mo
        (mkEffectU (Z_to_bv 64 a) [] (if prot =? PROT_NONE then [] else [(Z_to_bv 64 a, Z_to_bv 64 n)])
                                  (if prot =? PROT_NONE then [(Z_to_bv 64 a, Z_to_bv 64 n)] else []) [] [])
        (with_vmmaps (mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                        (if prot =? PROT_NONE then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) [].
Proof.
  intros len prot mo a h n Hlen Hp Ha Hal Hc Hrf Hl Hpl. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn. fold n in Hn.
  apply nstep_mmap_iff. split; [reflexivity|].
  assert (Herr : errno_ret_in mmap_errnos (Z_to_bv 64 a) = false).
  { destruct (errno_ret_in mmap_errnos (Z_to_bv 64 a)) eqn:E; [|reflexivity]. apply errno_ret_in_true in E as (e & He & E).
    cbn in He. destruct He as [<-|[]]. apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia. rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). unfold two_pow_64, ENOMEM in E. lia. }
  split; [| apply mmap_success_nonspurious; [reflexivity| exact Herr]]. unfold check_mmap, check_mmap_fixed_overflow.
  change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPF))) with false. cbv iota.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  assert (TAIL : forall noacc,
    (if (bv_unsigned (Z_to_bv 64 a) mod page_size =? 0) && (0 <? bv_unsigned (Z_to_bv 64 a)) && (bv_unsigned (Z_to_bv 64 a) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <=? alloc_top h)
        && region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
        && listNN_eqb [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))] [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))]
     then CheckOk (with_mmap_backing (Z_to_bv 64 MAPF) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
            (with_vmmaps (mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) :: vm_maps h) noacc
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo)) []
     else CheckReject)
    = CheckOk (with_vmmaps (mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h) noacc
                             (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo) []).
  { intros noacc. rewrite !unsigned_lit by lia. fold (mmap_len len). fold n. rewrite page_size_eq, Hal, Z.eqb_refl.
    rewrite (proj2 (Z.ltb_lt 0 a) Ha). rewrite (proj2 (Z.leb_le _ _) Hc), Hrf, listNN_eqb_refl. cbn [andb].
    rewrite with_mmap_backing_plain by reflexivity. reflexivity. }
  assert (Hbud : mmap_noreserve_backed_ok (Z_to_bv 64 MAPF) mo (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) = true).
  { rewrite mmap_noreserve_backed_ok_plain by reflexivity. rewrite unsigned_lit by lia. fold (mmap_len len) n h. apply Z.leb_le. exact Hl. }
  destruct Hp as [-> | ->].
  - change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
    change (PROT_NONE =? PROT_NONE) with true. cbv iota. fold h. cbv zeta. rewrite Herr.
    rewrite <- (TAIL ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h)). rewrite !unsigned_lit by lia.
    (* LPS 727298f3: the PROT_NONE arm tests the request's placement too *)
    try (fold (mmap_len len); fold n).
    rewrite ?page_size_eq, ?Hal, ?Z.eqb_refl, ?(proj2 (Z.ltb_lt 0 a) Ha), ?(proj2 (Z.leb_le _ _) Hc), ?Hrf, ?listNN_eqb_refl.
    (* LPS 727298f3: the freely placed arm declines on place_declined_b; the hint is NULL *)
    rewrite ?place_declined_b_null, ?Hpl. cbn [andb]. reflexivity.
  - change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
    change (PROT_RW =? PROT_NONE) with false. cbv iota. fold h. cbv zeta. rewrite Herr. rewrite Hbud.
    rewrite <- (TAIL (vm_noaccess h)). rewrite !unsigned_lit by lia.
    try (fold (mmap_len len); fold n).
    rewrite ?page_size_eq, ?Hal, ?Z.eqb_refl, ?(proj2 (Z.ltb_lt 0 a) Ha), ?(proj2 (Z.leb_le _ _) Hc), ?Hrf, ?listNN_eqb_refl.
    rewrite ?place_declined_b_null, ?Hpl. cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
Section Fixed.
Variables (a : Z) (mo : Model).
Let h := m_vmmaps mo.
Let aw := Z_to_bv 64 a.
Let nw := Z_to_bv 64 PGSZ.
Hypothesis Ha : 0 < a.
Hypothesis Hc : a + PGSZ <= alloc_top h.   (* [comment removed for export] *)
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hrf : region_free (vm_reserved h) aw nw = true.
Hypothesis Hmc : map_contains (vm_maps h) aw nw = true.

Definition fixed_done_h : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
Lemma check_mmap_fixed_gate : forall eff,
  check_mmap aw nw (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo =
  match eff with
  | mkEffectU r [] [] us [] [] =>
      if errno_ret_in mmap_errnos r
      then match us with
           | [] => CheckOk mo []
           | _ :: _ =>
               if listNN_eqb us [(aw, nw)]
               then CheckOk (with_mmap_destroyed aw nw (mmap_fixed_destroyed_next h aw nw) mo) []
               else CheckReject
           end
      else if bv_eqb r aw && listNN_eqb us [(aw, nw)]
      then CheckOk (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)) []
      else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros eff. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT. unfold check_mmap, check_mmap_fixed_overflow.
  change (negb (mmap_off_aligned_b (Z_to_bv 64 0))) with false. change (negb (mmap_anon_b (Z_to_bv 64 MAPFX))) with false.
  change (w_is0 nw) with false.
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
  change (mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with true. cbv iota beta.
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia). rewrite Un. change (page_round_up_Z PGSZ) with PGSZ. cbv zeta.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia). rewrite Ua.
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
  fold h. replace (a + PGSZ <=? alloc_top h) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
  rewrite page_size_eq, Hal. cbn [Z.eqb negb]. replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
  fold nw. fold h. rewrite Hrf, Hmc. cbn [andb]. rewrite Un.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  reflexivity.
Qed.

Lemma nstep_fixed_done_intro :
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo (mkEffectU aw [] [] [(aw, nw)] [] [])
        (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)) [].
Proof.
  assert (NE : errno_ret_in mmap_errnos aw = false).
  { pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
    destruct (errno_ret_in mmap_errnos aw) eqn:E; [|reflexivity]. apply errno_ret_in_true in E as (e & He & E).
    cbn in He. destruct He as [<-|[]]. apply (f_equal bv_unsigned) in E. subst aw.
    rewrite unsigned_lit in E by (unfold PGSZ in *; lia).
    rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). unfold two_pow_64, ENOMEM, PGSZ in *. lia. }
  apply nstep_mmap_iff. split; [reflexivity|]. fold aw nw. split.
  - rewrite check_mmap_fixed_gate. rewrite NE, bv_eqb_refl, listNN_eqb_refl. reflexivity.
  - apply mmap_success_nonspurious; [reflexivity| exact NE].
Qed.
Lemma m_vmmaps_fixed_done : m_vmmaps (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)) = fixed_done_h.
Proof. rewrite with_mmap_replacement_plain by reflexivity. rewrite m_vmmaps_vm_forget_range. apply m_vmmaps_with_vmmaps. Qed.
Lemma vm_only_fixed_done : vm_only mo (with_mmap_replacement (Z_to_bv 64 MAPFX) aw nw (with_vmmaps fixed_done_h mo)).
Proof.
  apply (vm_only_trans _ (with_vmmaps fixed_done_h mo)); [apply vm_only_with_vmmaps; reflexivity|]. apply vm_only_replacement_off. reflexivity.
Qed.
End Fixed.

(* [comment removed for export] *)
Definition munmap_h (h : VmMaps) (aw nw : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

(* [comment removed for export] *)
Lemma nstep_munmap_intro : forall a len mo,
  let h := m_vmmaps mo in let n := mmap_len len in let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  0 <= a -> a mod 4096 = 0 -> 0 < len -> a + n <= TASK_SIZE ->
  map_has (vm_maps h) aw nw = true ->
  (* LPS 727298f3: munmap subtracts the range from [vm_maps] *)
  maps_subtract (vm_maps h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = map_remove (vm_maps h) aw ->
  nstep (NMunmap a len) mo (mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [])
        (with_mmap_destroyed aw nw (munmap_h h aw nw) mo) [].
Proof.
  intros a len mo h n aw nw Ha Hal Hlen Hb Hhas Hex. pose proof (mmap_len_ge len Hlen) as Hn. fold n in Hn. pose proof TASK_SIZE_val as TS.
  apply nstep_munmap_iff. split; [|cbn [mm_ns node_input]; apply spurious_refusal_not_refusal; vm_compute; reflexivity].
  unfold check_munmap. fold aw h.

assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  replace (negb (bv_unsigned aw mod page_size =? 0)) with false by (rewrite Ua, page_size_eq, Hal; reflexivity).
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb negb orb]. cbv zeta.
  rewrite (unsigned_lit len) by lia. fold (mmap_len len). fold n nw.
  replace (TASK_SIZE <? bv_unsigned aw + n) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hhas. cbv iota.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  change (w_is0 (Z_to_bv 64 0)) with true. rewrite listNN_eqb_refl. cbn [andb].
  unfold munmap_h, mmap_fixed_destroyed_next. rewrite Hex. reflexivity.
Qed.

Lemma m_vmmaps_munmap : forall aw nw h mo, m_vmmaps (with_mmap_destroyed aw nw (munmap_h h aw nw) mo) = munmap_h h aw nw.
Proof. intros. apply m_vmmaps_with_mmap_destroyed. Qed.

(* [comment removed for export] *)
Section Mprotect.
Variables (a : Z) (mo : Model).
Let h := m_vmmaps mo.
Let aw := Z_to_bv 64 a.
Let nw := Z_to_bv 64 PGSZ.
Hypothesis Ha : 0 <= a.
Hypothesis Hb : a + PGSZ < 2^64.
Hypothesis Hal : a mod 4096 = 0.
Hypothesis Hcn : map_contains (vm_noaccess h) aw nw = true.
Hypothesis Hcm : map_contains (vm_maps h) aw nw = true.
(* LPS 727298f3: check_mprotect leaves a range meeting the vDSO pair unmodeled; this one misses it *)
Hypothesis Hvd : region_free (vdso_reserved (m_kernel mo) (vdso_top h)) aw nw = true.

Lemma check_mprotect_gate : forall eff,
  check_mprotect aw nw (Z_to_bv 64 PROT_RW) eff mo =
  match eff with
  | mkEffectU r [] zs [] [] [] =>
      if errno_ret_in mprotect_errnos r   (* [comment removed for export] *)
      then match zs with [] => CheckOk mo [] | _ => CheckReject end
      else if mprotect_budget_ok mo aw nw && w_is0 r && listNN_eqb zs [(aw, nw)]
      then CheckOk (mprotect_model_next mo aw nw) []
      else CheckReject
  | _ => CheckReject
  end.
Proof.
  intros eff. unfold check_mprotect.
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia). rewrite Ua, page_size_eq, Hal.
  change (w_is0 nw) with false. cbv iota. cbn [Z.eqb negb].
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia). rewrite Un. change (page_round_up_Z PGSZ) with PGSZ.
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia). cbv zeta. fold nw h.
  rewrite Hvd, Hcn, Hcm. reflexivity.
Qed.

Lemma nstep_mprotect_ok_intro :
  vm_live_bytes h <= vm_limit h -> minv mo ->
  nstep (NMprotect a PGSZ PROT_RW) mo (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] [])
        (mprotect_model_next mo aw nw) [].
Proof.
  intros Hl Hmi. apply nstep_mprotect_iff. fold aw nw.
  assert (Herr : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false).
  {
    destruct (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) eqn:E; [|reflexivity]. apply errno_ret_in_true in E as (e & He & E).
    cbn in He. destruct He as [<-|[]]. apply (f_equal bv_unsigned) in E. rewrite unsigned_lit in E by lia.
    rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). unfold two_pow_64, ENOMEM in E. lia. }
  split; [| apply mprotect_success_nonspurious; [reflexivity| exact Herr]]. rewrite check_mprotect_gate.
  assert (Hbud : mprotect_budget_ok mo aw nw = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
    eapply Z.le_trans; [apply backing_le_live| ].
    - unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. apply Hmi.
    - unfold mprotect_model_next. rewrite m_vm_materialized_with_vmmaps. apply Hmi.
    - unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit]. unfold vm_live_bytes in *. cbn [vm_maps]. exact Hl. }
  rewrite Herr, Hbud. change (w_is0 (Z_to_bv 64 0)) with true. rewrite listNN_eqb_refl. reflexivity.
Qed.

Lemma m_vmmaps_mprotect_next : m_vmmaps (mprotect_model_next mo aw nw) =
  mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. fold h.
  rewrite (unsigned_lit a) by (unfold PGSZ in *; lia). subst nw. rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). reflexivity.
Qed.
End Mprotect.
