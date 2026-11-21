(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef)): changed FULL0, FULL0_below, FULL0_low and 225 more; added AUXW, CHEAD, E00 and 67 more; removed W_range, hb_res, s0_fits; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/AsanPlanSoundSumsK.v, 952 lines within its lines 115-1674. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module AsanInitK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupAux OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanInitK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib7Mh_01329AsanInitK5argH0C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C59OSSVerify5KrLib7Mh_00387CatExec>valid_argv_lenC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3lebK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divK47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01C47Corelib5Lists7ListDef3nthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr05I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3orbK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4CEILC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C49OSSVerify5KrLib:AxSymRun3K9env_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=edenot_agree'C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3NX0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK:e_sp0_initC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib7Mh_01329AsanInitK5SINV0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2evC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib7Mh_01329AsanInitK2E0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2ebC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_01329AsanInitK;argH0_agreeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC45stdpp9bitvector;definitions7Z_to_bvC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathK47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathC46Stdlib5Lists4List:length_appI47Corelib4Init9Datatypes4prod00C47Corelib4Init3Nat3addC47Corelib4Init3Nat3mulC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout:auxv_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<string_addrsC49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8C46Stdlib5Lists4List8flat_mapC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?flatten_stringsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef6repeatC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC49OSSVerify5KrLib8PropExecAtotal_arg_bytes_ZC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecFlength_flatten_stringsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAlength_auxv_bytesC49OSSVerify5KrLib8PropExec@length_n_to_le_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecGlength_string_addrs_fstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecClength_flat_map_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutFlength_at_random_bytesC49OSSVerify5KrLib8PropExecAstring_addrs_pairC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK@stack_image_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst7Inj_Z_ZC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9auxv_sizeI47Corelib4Init5Logic5False00C49OSSVerify5KrLib8PropExecMbuild_stack_bytes_within_spanC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayoutAbuild_stack_bytesC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_spanC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00C46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib6ZArith4Zdiv:Zminus_modc59OSSVerify5KrLib7Mh_01329AsanInitK=length_bsb_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6bsb_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6len_evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6if_topC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<brk_aslr_maxC4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8BRK_ASLRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7usp_fitC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecBvalid_argv_str_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6usp_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6usp_hiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7W_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4V_S1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4V_S2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6V_ARGCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6V_ENVCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4V_L0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3V_WC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5V_BRKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5V_S2AC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_overflowC56Stdlib5Arith8PeanoNat3Nat;lt_ge_casesI47Corelib4Init5Peano2le00C56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_01329AsanInitK8L1_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4V_L1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5V_UIDC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<hwcap_rv64gcC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=hwcap_rv64gcvK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4mkMdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_mul64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:edenot_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:mkMd_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkAluC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkAlu_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics5Riscv3Sem7mul_divK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01c59OSSVerify5KrLib7Mh_01329AsanInitK6usp_alC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK3uE0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_sppgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7uE0_s2aC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6escaleC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4eaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK8u_e_sppgC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<e_sp0_unfoldC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib7Mh_01329AsanInitK7u_e_sp0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mod_addC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_lit64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5two64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_sub64C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9e_stk_lenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_envpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_auxvC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK8u_e_envpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK8u_e_auxvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_str0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_str1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK4Hav0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK8u_e_str0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:e_atrandomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_atr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5u_sp8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6model0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C59OSSVerify5KrLib>AsanPlanSoundK4APSK7fds_stdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5LIMITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4utopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7in_hullC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool;orb_false_rC4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib>AsanPlanSoundK4APSK8in_allowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6in_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK<model0_factsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5utop0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5FULL0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool:orb_true_rc59OSSVerify5KrLib7Mh_01329AsanInitK7hid0_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3hidC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z6leb_gtC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6ltb_ltC4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;Mr0_visibleC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9split_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK?split_lit_denotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib4Init5Logic9False_indK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6adenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;argH0_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4flatC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec>n_to_le_8_specC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK=rdn_Mr0_stackC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedc59OSSVerify5KrLib7Mh_01329AsanInitK9adenot_SAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout:auxv_wordsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc59OSSVerify5KrLib7Mh_01329AsanInitK7split_uC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout8auxv_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK9not_argH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout>read_auxv_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;kword_stackC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat3mulC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_auxbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK4Hhi'C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C56Stdlib6ZArith6BinInt1Z8max_specc59OSSVerify5KrLib7Mh_01329AsanInitK<auxv_word_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4auxwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;FULL0_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9elenZ_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK5elenZC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib>AsanPlanSoundK4APSK7u_smallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atc59OSSVerify5KrLib7Mh_01329AsanInitK9Mr0_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init5Logic4True01C49OSSVerify5KrLib8PropExec9read_argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ArgvEnv7u_argcNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?read_argv_ptr_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib7Mh_00419RefLayout>u_cat_argv_ptrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK4Hlo'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_lC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK8u_sltu64C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib7Mh_00419RefLayout>read_argv_nullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8kw_argv1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8e_argv1wC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c59OSSVerify5KrLib7Mh_01329AsanInitK8u_e_str1C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry03C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_reflK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout=at_random_offC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00238AsanCeilAfirstn1_skipn_nthC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_extractC47Corelib4Init5Logic7f_equalC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8ed_slackC4ELinuxProcessSemantics?LinuxProcessSem3Run;entry_slackC46Stdlib5Lists4List>nth_error_NoneC49OSSVerify5KrLib8PropExec=wrap_above_spC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_atrbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5K_RNDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK<u_e_atrandomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5vals0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01c59OSSVerify5KrLib7Mh_01329AsanInitK7if_hullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_loC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK9FULL0_lowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5if_rwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5rw_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6rw_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib7Mh_01329AsanInitK5if_phC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9ph_addr_zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8ph_ent_zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8ph_num_zC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC56Stdlib6ZArith4Znat3N2Z9is_nonnegC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5eaddzC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib7Mh_00419RefLayout=auxv_words_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7auxw_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<init_kn_withC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK5kr_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK9brk_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK?stack_window_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4V_HWC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib7Mh_01329AsanInitK8u_e_atr8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7u_sppg8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6uE0_L1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7uE0_uidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK8hw_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK6uE0_hwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK<argc_word_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK=argv0_word_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK=argv1_word_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_PHDRC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_PHENTC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_PHNUMC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout8AT_HWCAPC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_PAGESZC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout6AT_UIDC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_EUIDC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_SECUREC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9AT_RANDOMC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout7AT_NULLc59OSSVerify5KrLib7Mh_01329AsanInitK:atr_ptr_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7kimg_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK<rw_window_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK?init_kn_with_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;atrandom_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9init_regsC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4ridxC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:ridx_rangeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eqb_eqC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK>ridx_roundtripC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7eqb_neqC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C46Stdlib9micromega;ZifyClasses9not_morphc59OSSVerify5KrLib7Mh_01329AsanInitK=init_regs_nthC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7regs_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK2R0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto4kind02c59OSSVerify5KrLib7Mh_01329AsanInitK<edenot_e_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8pagedownC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6pageupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:shadow_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5sh_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK5sh_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allow1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7init_knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8vis_costC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;u_e_stk_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK7u_e_topC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9MBASE_MINC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3afd01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3hop00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK9if_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKEpageup_minus_pagedownC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;allowA_initC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6fds_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_tidsetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:maps_matchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_yloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7hole_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK4seps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra5iv_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeilEinit_sp_ok_init_modelC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8amap_denC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6am_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9sum_sizesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK8if_sizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State5Creds01K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01K4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State7mkModelC4ELinuxProcessSemantics?LinuxProcessSem5State:with_credsC4ELinuxProcessSemantics?LinuxProcessSem5State<with_urandomC4ELinuxProcessSemantics?LinuxProcessSem5State8with_netC4ELinuxProcessSemantics?LinuxProcessSem5State;with_nofileC4ELinuxProcessSemantics?LinuxProcessSem5State<with_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5StateCwith_abort_terminalC4ELinuxProcessSemantics?LinuxProcessSem5StateAin_abort_terminalC4ELinuxProcessSemantics?LinuxProcessSem5State:in_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem5State6in_netC4ELinuxProcessSemantics?LinuxProcessSem5State:in_urandomC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State6in_gidC4ELinuxProcessSemantics?LinuxProcessSem5State9in_groupsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00K46Stdlib5Lists4List5NoDup01C59OSSVerify5KrLib7Mh_00368AsanAcct=page_allowedbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00368AsanAcct4MInv01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8in_ghostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3RNAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3RLZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK;abytes_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK<init_regs_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK:init_kn_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsK59OSSVerify5KrLib>AsanPlanSoundK4APSK4seps01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_01329AsanInitK3inpC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7PID_MAXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC49OSSVerify5KrLib8PropExec9init_mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C49OSSVerify5KrLib8PropExec3fx0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~".  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition LIMIT : Z := target_alloc_limit.

(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47;
  (* [comment removed for export] *)
  if_resx  : (2 <= n_resx A)%nat /\ (20 <= p_resx A)%nat
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stack_image_size (sp top : word) : Z :=
  (bv_unsigned top - bv_unsigned sp)%Z.

(* [comment removed for export] *)
Lemma auxv_words_null : forall la ph entry uid gid hw ar ae,
  nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la))))
      (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0
  /\ nth (Z.to_nat (2 * (26 + 2 * rseq_z (la_rseq la)) + 1))
         (auxv_words la ph entry uid gid hw ar ae) (Z_to_bv 64 0) = Z_to_bv 64 0.
Proof. intros [ehdr c msz [|]] ph entry uid gid hw ar ae; split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma e_atrb_off : forall b, snd (e_atrb (rseq_z b)) = 24 + AUXSZ (rseq_z b).
Proof. intros [|]; vm_compute; reflexivity. Qed.

Section Init.
  Variable segs : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variable nofile : word.
  Variable sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  (* [comment removed for export] *)
  Variable kb : KernelBuild.
  (* [comment removed for export] *)
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  (* [comment removed for export] *)
  Variable apc : N.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry A.
  Definition inp : ProcInput :=
    mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw
      abrt Sv48 ur [] (recorded_kernel kb) execfn true sdf false.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch inp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp.
  (* [comment removed for export] *)

  Let entryw : word := Z_to_bv 64 (Z.of_N apc).
  (* [comment removed for export] *)
  Let la : LaunchAuxv := launch_auxv inp sp mbase.
  (* [comment removed for export] *)
  Let bsb := entry_stack_image inp mbase ph entryw sp rdraw.
  Let SIMG := entry_stack_image inp mbase ph entryw sp rdraw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [comment removed for export] *)
  Let rseq := kb_rseq (in_kernel inp).
  Let top := ed_top rdraw.
  Let utop := bv_unsigned top.
  (* [comment removed for export] *)
  Let G := Z.of_nat (block_items argv envp mod 2).
  (* [comment removed for export] *)
  Let W := Z.of_nat (block_pad_len rseq sp top argv envp execfn).
  (* [comment removed for export] *)
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  (* [comment removed for export] *)
  Let RZ := rseq_z rseq.
  (* [comment removed for export] *)
  Let CHEAD := Z.of_nat (block_head_size rseq argv envp).
  (* [comment removed for export] *)
  Let LSTR := Z.of_nat (launch_string_bytes argv envp execfn).

  (* [comment removed for export] *)
  Lemma inp_argv : in_argv inp = argv.        Proof. reflexivity. Qed.
  Lemma inp_envp : in_envp inp = envp.        Proof. reflexivity. Qed.
  Lemma inp_execfn : in_execfn inp = execfn.  Proof. reflexivity. Qed.
  Lemma inp_rseq : kb_rseq (in_kernel inp) = rseq. Proof. reflexivity. Qed.

  Definition vals0 : list word :=
    [Z_to_bv 64 (usp / 32768); Z_to_bv 64 argc; Z_to_bv 64 envc; Z_to_bv 64 L0; Z_to_bv 64 W;
     Z_to_bv 64 (bv_unsigned brk0 / 4096); Z_to_bv 64 ((usp mod 4096) / 16); Z_to_bv 64 L1; uid; hw;
     Z_to_bv 64 ((usp mod 32768) / 4096); Z_to_bv 64 G;
     (* [comment removed for export] *)
     gid].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool :=
    let z := bv_unsigned a in
    ((uE E e_sp0 <=? z) &&
     (((usp + 24 <=? z) && (z <? usp + 8 * argc + 8 * envc + 24))
      (* [comment removed for export] *)
      || ((STR0 <=? z) && (z <? utop))))%bool.

  Definition SINV0 (E : env) (M : word -> option byte) : Prop :=
    (forall n, (n < NX0)%nat -> ev E n = ev E0 n)
    /\ (forall a, argH0 E a = true -> M a = wrap_mem inp mbase ph entryw sp rdraw a).

  (* [comment removed for export] *)
  Lemma argH0_high : forall E a, argH0 E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Proof.
    (* [comment removed for export] *)
    intros E a H. unfold argH0 in H. destruct Hsp as [Hlo _]. unfold sp_window_lo in Hlo. unfold CEIL.
    pose proof (valid_argv_len argv Hva).
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)).
    apply andb_prop in H as [HS H]. apply Z.leb_le in HS.
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H;
      unfold usp, argc, envc, STR0 in H; lia.
  Qed.

  Lemma e_sp0_init : expr_vars_lt NX0 e_sp0 = true.
  Proof. reflexivity. Qed.

  Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof.
    intros E E' a Hag. unfold argH0, uE. rewrite (APSK.edenot_agree' NX0 E E' e_sp0 Hag e_sp0_init). reflexivity.
  Qed.

  Lemma SINV0_frame : forall E M M', (forall a, argH0 E a = true -> M' a = M a) -> SINV0 E M -> SINV0 E M'.
  Proof. intros E M M' Hf [H1 H2]. split; [exact H1|]. intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha. Qed.

  Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M HAG [H1 H2]. pose proof HAG as [Hag _]. split.
    - intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
    - intros a Ha. apply H2. rewrite (argH0_agree E E' a HAG). exact Ha.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z.
  Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z.
  Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hsp as (?&?&?); assumption. Qed.
  Lemma Hav0 : (0 < length argv)%nat.
  Proof. destruct Hva as [[? ?] _]; lia. Qed.

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  Lemma RZ_range : 0 <= RZ <= 1.
  Proof. exact (rseq_z_range rseq). Qed.

  (* [comment removed for export] *)
  Lemma auxv_count_RZ : Z.of_nat (auxv_count rseq) = 27 + 2 * RZ.
  Proof. unfold RZ, rseq_z, auxv_count. destruct (kb_rseq (in_kernel inp)); reflexivity. Qed.

  Lemma gap_range : 0 <= G <= 1.
  Proof. unfold G. pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia. Qed.

  (* [comment removed for export] *)
  Lemma chead_eq : CHEAD = 8 * argc + 8 * envc + 472 + 32 * RZ + 8 * G.
  Proof.
    pose proof (AUXSZ_of rseq) as HA. unfold AUXSZ in HA. change (rseq_z rseq) with RZ in HA.
    unfold CHEAD, G, argc, envc, block_head_size, block_items.
    lia.
  Qed.

  Lemma chead_range : 480 <= CHEAD <= 10752.
  Proof.
    pose proof chead_eq. pose proof len_av. pose proof len_ev. pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lstr_lo : 2 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma s0_in_strings : L0 + 1 <= LSTR.
  Proof.
    unfold LSTR, launch_string_bytes, L0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    pose proof Hav0 as Hnz.
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lstr_hi : LSTR + 8 * argc + 8 * envc <= 2097152.
  Proof.
    destruct Hlaunch as [_ Hb]. unfold launch_bytes, e2big_limit in Hb.
    rewrite inp_argv, inp_envp, inp_execfn in Hb. unfold LSTR, argc, envc. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pad_bounds_Z : 0 <= utop - 8 - LSTR - usp - CHEAD <= 4110.
  Proof.
    destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    rewrite inp_argv, inp_envp, inp_execfn, inp_rseq in Hslo, Hshi.
    change (ed_top rdraw) with top in Hslo, Hshi.
    fold LSTR in Hslo, Hshi. fold CHEAD in Hslo, Hshi. fold utop usp in Hslo, Hshi.
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (utop - 8 - LSTR - 4095) 16 ltac:(lia)).
    lia.
  Qed.

  Lemma pad_eq : W = utop - 8 - LSTR - usp - CHEAD.
  Proof.
    pose proof pad_bounds_Z.
    unfold W, block_pad_len, LSTR, CHEAD, utop, usp in *.
    rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pad_range : 0 <= W <= 4110.
  Proof. pose proof pad_bounds_Z. pose proof pad_eq. lia. Qed.

  Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size sp top.
  Proof.
    unfold bsb, stack_image_size.
    exact (length_entry_stack_image_launch Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma length_bsb_sum : Z.of_nat (length bsb) = CHEAD + W + LSTR + 8.
  Proof.
    pose proof pad_eq. rewrite length_bsb_eq. unfold stack_image_size. fold utop usp. lia.
  Qed.

  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof.
    unfold usp, bsb.
    exact (entry_stack_image_no_wrap Sv48 inp mbase ph entryw sp brk0 rdraw Hlau).
  Qed.

  Lemma bsb_len_hi : Z.of_nat (length bsb) <= 2101782.
  Proof. unfold bsb. exact (bsb_bound Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau). Qed.

  Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size. fold utop usp.
    pose proof (entry_page_top_within_window Sv48 inp mbase sp brk0 rdraw Hlau) as H.
    unfold entry_page_top, va_stack_top, sp_window_hi in H. fold top utop in H. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bsb_ge : 8 * argc + 8 * envc + 482 <= Z.of_nat (length bsb).
  Proof.
    pose proof length_bsb_sum. pose proof chead_eq. pose proof lstr_lo. pose proof pad_range.
    pose proof gap_range. pose proof RZ_range. lia.
  Qed.

  Lemma str0_hi : STR0 + LSTR + 8 = utop.
  Proof.
    unfold STR0, cat_string_off. pose proof pad_eq.
    fold CHEAD. fold W. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as Gb. pose proof len_av. pose proof len_ev. lia. Qed.

  (* [comment removed for export] *)
  Lemma uE0 :
    uE E0 (EVar V_S1) = usp / 32768 /\ uE E0 (EVar V_S2) = (usp mod 4096) / 16
    /\ uE E0 (EVar V_ARGC) = argc /\ uE E0 (EVar V_ENVC) = envc /\ uE E0 (EVar V_L0) = L0
    /\ uE E0 (EVar V_W) = W /\ uE E0 (EVar V_BRK) = bv_unsigned brk0 / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof gap_range.
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0_s2a : uE E0 (EVar V_S2A) = (usp mod 32768) / 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold uE. cbn [edenot E0 ev nth vals0 V_S2A].
    rewrite u64_lit by lia. reflexivity.
  Qed.

  Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  Lemma edenot_uid : uid = edenot E0 (EVar V_UID).
  Proof. reflexivity. Qed.

  Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  Lemma uE0_hw : uE E0 (EVar V_HW) = bv_unsigned hw.
  Proof. reflexivity. Qed.
  Lemma hw_range : bv_unsigned hw = 0x112d \/ bv_unsigned hw = 0x20112d.
  Proof. destruct Hhw as [-> | ->]; [left|right]; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma u_e_sppg : uE E0 e_sppg = usp / 4096 * 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_s2a as U2A.
    unfold e_sppg, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2A.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof u_e_sppg as UP.
    rewrite e_sp0_unfold. unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite UP, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  (* [comment removed for export] *)
  Lemma u_e_top : uE E0 e_top = usp / 4096 * 4096 - 8388608.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold e_top, eaddz, uE. rewrite mkAlu_denot, edenot_lit.
    pose proof u_e_sppg as U. unfold uE in U. rewrite u_add64, U, u_lit64. unfold two64.
    replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
    replace (usp / 4096 * 4096 + (2 ^ 64 - 8388608)) with ((usp / 4096 * 4096 - 8388608) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
  Qed.
  Lemma u_e_stk_len : uE E0 e_stk_len = 2 ^ 47 + 8388608 - usp / 4096 * 4096.
  Proof.
    pose proof usp_lo. pose proof usp_hi. unfold e_stk_len, esub, uE. rewrite mkAlu_denot, edenot_lit.
    pose proof u_e_sppg as U. unfold uE in U. rewrite u_sub64, U, u_lit64. unfold two64.
    rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia. rewrite Z.mod_small; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_sp8 : uE E0 e_sp8 = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _). pose proof uE0_s2a as U2A.
    unfold e_sp8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2, U2A.
    rewrite !Z.mod_small by lia. lia.
  Qed.
  Lemma u_sppg8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 512 (EVar V_S2A))) = usp / 4096 * 512.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & _). pose proof uE0_s2a as U2A.
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2A.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma uE0_G : uE E0 (EVar V_G) = G.
  Proof.
    pose proof gap_range. unfold uE. cbn [edenot E0 ev nth vals0 V_G].
    rewrite u64_lit by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_atrandom : uE E0 (e_atrandom RZ) = usp + CHEAD - 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof u_e_auxv as UA. pose proof uE0_G as UG.
    unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UG.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_str0 : uE E0 (e_str0 RZ) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof pad_range. pose proof pad_eq. pose proof lstr_lo.
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_atrandom as UA.
    unfold e_str0, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite UA, U6.
    rewrite !Z.mod_small by lia.
    unfold STR0, cat_string_off. fold CHEAD. fold W. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_str1 : uE E0 (e_str1 RZ) = STR0 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof gap_range. pose proof RZ_range.
    pose proof pad_range. pose proof pad_eq. pose proof str0_hi. pose proof s0_in_strings.
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *.
    rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + G.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof gap_range.
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8. pose proof uE0_G as UG.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot.
    rewrite !u_add64 by lia. rewrite U8, U3, U4, UG. rewrite !Z.mod_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem inp mbase ph entryw sp rdraw.
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_vdso (Vdso.vdso_run_init (ed_vdso rdraw))
      (init_model (segments_reserved segs) brk0 mbase sp LIMIT inp).

  Let cs0 := init_acs_of RZ A.
  Let hid0 := hid A argH0 E0 cs0 model0.
  Let Mr0 := Mr A argH0 E0 cs0 model0 FULL0.

  (* [comment removed for export] *)
  Let VTOP : Z :=
    page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  Let RESX : list (word * word) := vdso_reserved (in_kernel inp) VTOP.

  Lemma sum_sizes_app : forall l1 l2, APSK.sum_sizes (l1 ++ l2) = APSK.sum_sizes l1 + APSK.sum_sizes l2.
  Proof.
    induction l1 as [|iv l1 IH]; intro l2; cbn [app APSK.sum_sizes]; [lia|]. rewrite IH. lia.
  Qed.

  Lemma mb_range : mmap_base_min <= bv_unsigned mbase <= mmap_base_max
                   /\ bv_unsigned mbase mod page_size = 0.
  Proof. destruct Hmb as (Y1 & Y2 & Y3). repeat split; assumption. Qed.

  Lemma vtop_range : mmap_base_min - 4095 <= VTOP <= bv_unsigned mbase
                     /\ VTOP mod 4096 = 0.
  Proof.
    pose proof mb_range as ((Y1 & Y2) & Y3). pose proof usp_lo.
    unfold VTOP, page_round_down_Z, page_size, stack_max_size,
           mmap_base_min, mmap_base_max, sp_window_hi, usp in *.
    split; [split|]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma resx_shape :
    RESX = [(Z_to_bv 64 (VTOP - vdso_len (in_kernel inp)), Z_to_bv 64 (vdso_vvar_pages * page_size));
            (Z_to_bv 64 (VTOP - vdso_len (in_kernel inp) + vdso_vvar_pages * page_size),
             Z_to_bv 64 (vdso_text_pages (in_kernel inp) * page_size))].
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof (vdso_len_bounds (in_kernel inp)).
    unfold RESX, vdso_reserved. cbv zeta.
    replace (VTOP - vdso_len (in_kernel inp) <? page_size) with false
      by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
    reflexivity.
  Qed.

  Lemma resx_len : (length RESX <= 2)%nat.
  Proof. rewrite resx_shape. cbn [length]. lia. Qed.

  Lemma resx_sum : APSK.sum_sizes RESX = vdso_len (in_kernel inp).
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
    rewrite resx_shape. cbn [APSK.sum_sizes fst snd].
    unfold vdso_len, vdso_vvar_pages, page_size in *.
    rewrite !u64_lit by lia. lia.
  Qed.

  Lemma resx_bytes_lo : 81920 <= resx_bytes A.
  Proof.
    pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. unfold resx_bytes. lia.
  Qed.

  Lemma resx_ok : Forall (APSK.resx_entry_ok A) RESX.
  Proof.
    pose proof vtop_range as [[T1 T2] T3]. pose proof mb_range as ((Y1 & Y2) & Y3).
    pose proof (if_hull _ _ _ IMG) as (G1 & G2 & G3 & G4).
    pose proof (vdso_text_pages_pos (in_kernel inp)). pose proof (vdso_text_pages_le (in_kernel inp)).
    rewrite resx_shape. unfold APSK.resx_entry_ok, vdso_len, vdso_vvar_pages, page_size in *.
    repeat constructor; cbn [fst snd];
      rewrite !u64_lit by (unfold mmap_base_min, mmap_base_max, sp_window_hi in *; lia);
      unfold KHI, mmap_base_min, mmap_base_max, sp_window_hi in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma model0_facts :
    m_halted model0 = None /\ m_fds model0 = fds_std /\ m_tid model0 = None
    /\ vm_reserved (m_vmmaps model0) = segments_reserved segs ++ RESX
    /\ vm_maps (m_vmmaps model0) = []
    /\ vm_noaccess (m_vmmaps model0) = [] /\ m_vm_lazy model0 = [] /\ m_vm_materialized model0 = []
    /\ vm_limit (m_vmmaps model0) = LIMIT /\ vm_brk (m_vmmaps model0) = brk0 /\ vm_start_brk (m_vmmaps model0) = brk0
    /\ vm_mmap_base (m_vmmaps model0) = mbase /\ eager_used model0 = 0.
  Proof. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma utop0 : APSK.utop E0 = usp / 4096 * 4096 - 8388608.
  Proof. unfold APSK.utop, APSK.pagedown. rewrite u_e_sp0. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hid0_eq : forall a : word, hid0 a = (argH0 E0 a || negb (APSK.in_hull A (bv_unsigned a) || (usp / 4096 * 4096 - 8388608 <=? bv_unsigned a)))%bool.
  Proof.
    intros a. unfold hid0, hid, vis. rewrite utop0. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (usp / 4096 * 4096 - 8388608 <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia). rewrite orb_true_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma FULL0_below : forall a : word, usp - 6144513 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (HW : stack_window_lo (in_kernel inp) mbase rdraw
                 <= bv_unsigned sp + stack_window_reach - stack_max_size)
      by exact (stack_window_lo_valid inp sp brk0 mbase rdraw Hlaunch Hlau).
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_window_reach, stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    pose proof (stack_window_lo_ge_sp inp sp brk0 mbase rdraw Hlau) as HW.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (stack_window_lo (in_kernel inp) mbase rdraw) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr0_stack : forall (a : word) n,
    usp <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
    (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> argH0 E0 x = false) ->
    rdn segs Mr0 a n = rdn segs (stack_to_mem sp SIMG) a n.
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
    rewrite <- (rdn_wrap_stack_above segs inp mbase ph entryw sp rdraw a n) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp, CEIL in *; lia | apply Hvis; exact Hx].
  Qed.

  Lemma split_u : forall E e b k, split_lit e = (b, k) -> 0 <= k -> k <= uE E e ->
    bv_unsigned (edenot E b) + k = uE E e.
  Proof.
    intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma argH0_range : forall a : word, argH0 E0 a = true ->
    usp + 24 <= bv_unsigned a < usp + 8 * argc + 8 * envc + 24
    \/ STR0 <= bv_unsigned a < utop.
  Proof.
    intros a H. unfold argH0 in H. apply andb_prop in H as [_ H].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
      apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left | right]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma not_argH0 : forall a : word,
    (bv_unsigned a < usp + 24 \/ (usp + 8 * argc + 8 * envc + 24 <= bv_unsigned a < STR0)
     \/ utop <= bv_unsigned a) -> argH0 E0 a = false.
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    (* [comment removed for export] *)
    pose proof len_av. pose proof len_ev. pose proof chead_eq. pose proof pad_range.
    pose proof gap_range. pose proof str0_hi. pose proof pad_eq. pose proof lstr_lo.
    pose proof RZ_range. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kword_stack : forall b k v (w : word),
    bv_unsigned (edenot E0 b) + k = bv_unsigned w ->
    usp <= bv_unsigned w -> bv_unsigned w + 8 <= usp + Z.of_nat (length bsb) ->
    (forall x : word, bv_unsigned w <= bv_unsigned x < bv_unsigned w + 8 -> argH0 E0 x = false) ->
    rdn segs (stack_to_mem sp SIMG) w 8%nat = Some (word_le8 (edenot E0 v)) ->
    kentry_ok segs E0 Mr0 (KWord (SA b k) 8 v).
  Proof.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Let AUXW := auxv_words la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn).

  (* [comment removed for export] *)
  Lemma auxv_word_ok : forall (j : nat) v,
    (j < 2 * auxv_count rseq)%nat ->
    nth j AUXW (Z_to_bv 64 0) = edenot E0 v ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 8 * Z.of_nat j)) 8 v).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    pose proof auxv_count_RZ.
    (* [comment removed for export] *)
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
    - rewrite <- Hv.
      exact (read_auxv_word segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi' j Hj).
  Qed.

  (* [comment removed for export] *)
  Lemma auxw_ok : forall i ty v,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    nth (Z.to_nat (2 * i + 1)) AUXW (Z_to_bv 64 0) = edenot E0 v ->
    know_ok segs E0 Mr0 (auxw i ty v).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma Mr0_below : forall a : word, usp - stack_window_depth <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av. pose proof stack_window_depth_val.
    rewrite Mr0_visible; [apply FULL0_below; lia | lia | apply not_argH0; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma stack_window_ok :
    kentry_ok segs E0 Mr0 (KWr (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth))
    /\ kentry_ok segs E0 Mr0 (KZero (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth)).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof stack_window_depth_val as HD.
    assert (Hst : estart E0 (SA e_sp0 (-stack_window_depth)) = usp - stack_window_depth).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit stack_window_depth) = stack_window_depth) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-stack_window_depth)) (elenZ E0 (ELit stack_window_depth))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc inp mbase ph entryw segs sp rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3.
        pose proof len_av. unfold len_word, argc in *. rewrite u64_lit by lia. reflexivity. }
      rewrite inp_argv in RW. rewrite <- Hv. apply RW. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cat_argv0_eq :
    bv_unsigned (cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0) = STR0.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0 Hav0).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
    change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
    change (in_argv inp) with argv. change (in_envp inp) with envp.
    unfold STR0, CHEAD, W, usp, rseq, top, cat_string_off in *.
    rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia.
  Qed.

  Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 (e_str0 RZ)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    apply (kword_stack e_sp0 8 (e_str0 RZ) (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 0) as RW.
      assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                   = edenot E0 (e_str0 RZ)).
      { apply bv_eq. rewrite cat_argv0_eq. pose proof u_e_str0 as U. unfold uE in U. rewrite U. reflexivity. }
      rewrite <- Hv. apply RW; [exact Hav0|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 (e_argv1w RZ)).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 (e_argv1w RZ) = if (1 <? argc) then edenot E0 (e_str1 RZ) else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 (e_str1 RZ))).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 (e_argv1w RZ) (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k segs inp mbase ph entryw sp rdraw 1) as RW.
        assert (Hv : cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1
                     = edenot E0 (e_str1 RZ)).
        { apply bv_eq.
          pose proof chead_eq. pose proof pad_range. pose proof gap_range. pose proof length_bsb_sum. pose proof RZ_range.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          pose proof (TF argv Hav0) as TF0.
          pose proof u_e_str1 as U. unfold uE in U.
          rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 1 Hav1).
          rewrite (cat_string_base_offset Sv48 inp mbase sp brk0 rdraw Hlau).
          change (kb_rseq (in_kernel inp)) with rseq. change (in_execfn inp) with execfn.
          change (in_argv inp) with argv. change (in_envp inp) with envp.
          rewrite U. unfold STR0, CHEAD, W, usp, L0, rseq, top, cat_string_off in *.
          rewrite nat_to_word_add_merge, word_add_nat, u64_lit by lia. lia. }
        rewrite <- Hv. apply RW; [exact Hav1|]. fold bsb. pose proof bsb_nw. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as RW.
        rewrite inp_argv in RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst (e_atrb RZ)) (snd (e_atrb RZ))) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range.
    (* [comment removed for export] *)
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
    set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
    pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by exact (e_atrb_off rseq). unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + CHEAD - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & Hmod & Hrd)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff, Hrd.
    assert (Hu : bv_unsigned (at_random_ptr sp rseq argv envp) = usp + CHEAD - 16).
    { rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia). unfold CHEAD. lia. }
    (* [comment removed for export] *)
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold SIMG in Hrd.
    rewrite (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp rseq argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + CHEAD - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp, CEIL in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + CHEAD - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + CHEAD - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      (* [comment removed for export] *)
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
      replace (usp + CHEAD - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.


  Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  Lemma atr_ptr_eq : at_random_ptr sp rseq argv envp = edenot E0 (e_atrandom RZ).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof chead_eq. pose proof chead_range. pose proof gap_range.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb. pose proof RZ_range.
    destruct (at_random_off segs Sv48 inp mbase ph entryw sp brk0 rdraw Hlaunch Hlau Hhi') as [off (Hp & Hoff & _ & _)].
    rewrite inp_argv, inp_envp, inp_rseq in Hp, Hoff.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold CHEAD, usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold CHEAD, usp. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma auxv_null_ok : know_ok segs E0 Mr0 (auxw (26 + 2 * RZ) 0 (ELit 0)).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    destruct (auxv_words_null la ph entryw uid gid hw
                (at_random_ptr sp rseq argv envp) (at_execfn_ptr top execfn)) as [N1 N2].
    apply auxw_ok; [lia | exact N1 | rewrite edenot_lit; exact N2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma auxt_ok : forall i ty,
    (0 <= i < Z.of_nat (auxv_count rseq)) ->
    nth (Z.to_nat (2 * i)) AUXW (Z_to_bv 64 0) = Z_to_bv 64 ty ->
    kentry_ok segs E0 Mr0 (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit ty)).
  Proof.
    intros i ty Hi H1.
    replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia.
    apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma auxv_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb)) (ELit (AUXSZ RZ))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    (* [comment removed for export] *)
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + 8 * argc + 8 * envc + 24) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit (AUXSZ RZ)) = AUXSZ RZ) by (apply elenZ_lit; unfold AUXSZ; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. unfold AUXSZ in *.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
    replace (usp + 8 * argc + 8 * envc + 24 + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma auxv_rseq_ok :
    know_ok segs E0 Mr0 (if Z.eqb RZ 1 then auxw 26 27 (ELit 28) ++ auxw 27 28 (ELit 32) else []).
  Proof.
    pose proof auxv_count_RZ. pose proof RZ_range.
    unfold RZ, rseq, rseq_z in *. unfold AUXW, la, launch_auxv in *.
    (* [comment removed for export] *)
    destruct (Bool.bool_dec (kb_rseq (in_kernel inp)) true) as [Hr|Hr]; [| apply Bool.not_true_is_false in Hr];
      rewrite Hr; cbn [Z.eqb Pos.eqb]; [|constructor].
    apply Forall_app; split; apply auxw_ok;
      unfold AUXW, rseq, la, launch_auxv, auxv_words, auxv_entries, auxv_count in *; cbn [la_rseq];
      rewrite ?Hr;
      first [ (cbn; lia)
            | (cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
               first [reflexivity | (rewrite edenot_lit; reflexivity)])
            | fail 1 "OSSV467-AUXRSEQ:" ].
  Qed.

  (* [comment removed for export] *)
  Lemma gap_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst e_auxb) (snd e_auxb + AUXSZ RZ)) (escale 8 (EVar V_G))).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof bsb_ge as Gb. pose proof RZ_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab (ak + AUXSZ RZ)) = usp + 8 * argc + 8 * envc + 24 + AUXSZ RZ)
      by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (escale 8 (EVar V_G)) = 8 * G).
    { pose proof uE0_G as UG. unfold elenZ, escale, uE in *. rewrite mkMd_denot, edenot_lit.
      rewrite u_mul64, u64_lit, UG by lia. rewrite Z.mod_small by lia. reflexivity. }
    cbn [kentry_ok]. rewrite Hst, Hl. unfold AUXSZ in *.
    split; [unfold flat; rewrite Hst; unfold AUXSZ, usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + 8 * argc + 8 * envc + 24 + (432 + 32 * RZ) + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
    replace (usp + 8 * argc + 8 * envc + 24 + (432 + 32 * RZ) + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  Lemma pad_unk_ok : kentry_ok segs E0 Mr0 (KUnk (SA (fst (e_atrb RZ)) (snd (e_atrb RZ) + 16)) (EVar V_W)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as Gb.
    pose proof chead_eq. pose proof chead_range. pose proof pad_range. pose proof gap_range.
    pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range.
    pose proof str0_hi. pose proof pad_eq.
    assert (Hab : split_lit (e_atrandom RZ) = (fst (e_atrb RZ), snd (e_atrb RZ))) by (unfold e_atrb; destruct (split_lit (e_atrandom RZ)); reflexivity).
    set (ab := fst (e_atrb RZ)) in *. set (ak := snd (e_atrb RZ)) in *.
    pose proof (split_u E0 (e_atrandom RZ) ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 24 + AUXSZ RZ) by exact (e_atrb_off rseq). unfold AUXSZ in Hak.
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab (ak + 16)) = usp + CHEAD) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (EVar V_W) = W) by (destruct uE0 as (_ & _ & _ & _ & _ & U6 & _); exact U6).
    cbn [kentry_ok]. rewrite Hst, Hl.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp inp mbase ph entryw sp rdraw _) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    unfold stack_to_mem. fold usp. rewrite u64_lit by (unfold usp in *; lia).
    replace (usp <=? usp + CHEAD + i) with true by (symmetry; apply Z.leb_le; lia).
    cbv zeta.
    assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, bsb; lia).
    replace (usp + CHEAD + i - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
    intros Hn. apply nth_error_None in Hn. lia.
  Qed.

  Lemma auxv_rest_ok : know_ok segs E0 Mr0 (auxv_rest RZ A).
  Proof.
    pose proof RZ_range. pose proof auxv_count_RZ.
    unfold auxv_rest.
    (* [comment removed for export] *)
    do 6 (apply Forall_app; split;
      [ apply auxw_ok;
        [ lia
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          reflexivity
        | unfold AUXW, auxv_words, auxv_entries;
          cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
          first [ reflexivity
                | (rewrite edenot_lit; reflexivity)
                | (rewrite edenot_lit; unfold entryw; rewrite Hapc; reflexivity)
                | fail 1 "OSSV467-AUXREST-PAIR:" ] ]
      | ]).
    apply Forall_app; split; [exact auxv_rseq_ok|].
    apply Forall_cons; [exact auxv_unk_ok|].
    (* [comment removed for export] *)
    do 11 (apply Forall_cons;
      [ first [ (apply auxt_ok;
                 [ lia
                 | unfold AUXW, auxv_words, auxv_entries;
                   cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
                   reflexivity ])
              | fail 1 "OSSV467-AUXT:" ] |]).
    apply Forall_cons; [exact gap_unk_ok|].
    apply Forall_cons; [exact pad_unk_ok|].
    apply Forall_nil.
  Qed.

  Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with RZ atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof pad_range. pose proof gap_range. pose proof chead_range.
    (* [comment removed for export] *)
    pose proof chead_eq. pose proof length_bsb_sum. pose proof lstr_lo. pose proof RZ_range. pose proof auxv_count_RZ.
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as Gb. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    unfold init_kn_with.
    (* [comment removed for export] *)
    remember (auxv_rest RZ A) as REST eqn:EREST.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_s2a; lia|].   (* [comment removed for export] *)
      (* [KRange (e_str0 RZ) 0x7fff800000c0 0x800000000000], argv[0]'s address:
         [STR0 + LSTR + 8 = utop] ([str0_hi]) with [utop - usp = |bsb|]
         ([length_bsb_eq]) and [usp + |bsb| <= 2^47] ([usp_fit]) above, and
         [STR0 = usp + CHEAD + W] ([length_bsb_sum]) with [usp_lo] below. *)
      apply Forall_cons; [apply kr_ok; rewrite u_e_str0; pose proof str0_hi as S0;
                          pose proof length_bsb_eq as LE; unfold stack_image_size in LE; fold utop usp in LE; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; lia|].
      (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite u_e_auxv; unfold AUXSZ; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sppg; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite u_sppg8; lia|].   (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_hw; pose proof hw_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      (* [comment removed for export] *)
      apply Forall_cons; [apply kr_ok; rewrite uE0_G; pose proof gap_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    (* [comment removed for export] *)
    10: exact auxv_null_ok.
    (* [comment removed for export] *)
    9: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           reflexivity
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           exact atr_ptr_eq ].
    (* [comment removed for export] *)
    1-8: apply auxw_ok;
         [ lia
         | unfold AUXW, auxv_words, auxv_entries;
           cbn [flat_map fst snd app nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul];
           try reflexivity .. ].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
    rewrite EREST. exact auxv_rest_ok.
  Qed.

  Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn RZ A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  Lemma init_regs_ok : regs_ok E0 init_regs R0.
  Proof.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma allowA_init : allowA A E0 cs0 =
    [(pagedown (img_lo A), pageup (img_lo A + (img_hi A - img_lo A)));
     (pagedown (shadow_off A + img_lo A / 8), pageup (shadow_off A + (img_lo A + (img_hi A - img_lo A)) / 8));
     (pagedown (usp / 4096 * 4096 - 8388608), pageup ((usp / 4096 * 4096 - 8388608) + (2 ^ 47 + 8388608 - usp / 4096 * 4096)));
     (pagedown (shadow_off A + (usp / 4096 * 4096 - 8388608) / 8),
      pageup (shadow_off A + ((usp / 4096 * 4096 - 8388608) + (2 ^ 47 + 8388608 - usp / 4096 * 4096)) / 8))].
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map allow1 fst snd].
    unfold sh_lo, sh_hi. cbn [fst snd]. rewrite !u_e_top, !u_e_stk_len.
    unfold uE. rewrite !edenot_lit, !u64_lit by (unfold CEIL; lia). reflexivity.
  Qed.

  Lemma abytes_init : A_bytes (allowA A E0 cs0) <= vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL)
                      /\ vis_cost (img_hi A - img_lo A) + vis_cost (2 ^ 47 - CEIL) <= LIMIT.
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1.
    pose proof usp_lo as UL. pose proof usp_hi as UH.
    rewrite allowA_init. cbn [A_bytes fst snd]. unfold vis_cost, CEIL, LIMIT, target_alloc_limit.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    set (P := usp / 4096 * 4096). assert (HP : usp - 4095 <= P <= usp) by (unfold P; lia).   (* [comment removed for export] *)
    replace ((P - 8388608) + (2 ^ 47 + 8388608 - P)) with (2 ^ 47) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    rewrite (P2 (2 ^ 47) eq_refl).
    assert (PD : forall z, z - 4095 <= pagedown z <= z) by (intros z; unfold pagedown; lia).
    pose proof (PD (P - 8388608)).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    pose proof (pageup_minus_pagedown (shadow_off A + (P - 8388608) / 8) (shadow_off A + 2 ^ 47 / 8) ltac:(lia)).
    clearbody P. split; lia.
  Qed.

  Theorem init_cs_ok : cs_ok segs A LIMIT SINV0 argH0 fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      pose proof (if_resx _ _ _ IMG) as [RX1 RX2]. pose proof resx_bytes_lo.
      pose proof (vdso_len_bounds (in_kernel inp)).
      exists RESX. split; [reflexivity|].
      split; [exact resx_ok|].
      split; [pose proof resx_len; lia | rewrite resx_sum; unfold page_size in *; lia].
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - (* [comment removed for export] *)
      rewrite app_nil_r, sum_sizes_app, (if_sizes _ _ _ IMG), resx_sum.
      pose proof (vdso_len_bounds (in_kernel inp)). pose proof resx_bytes_lo.
      unfold page_size in *. lia.
    - (* [comment removed for export] *) rewrite u_e_sp0, u_e_sppg. unfold APSK.pagedown, model0, with_vdso, init_model, usp. cbn -[Z.mul Z.div Z.sub Z.add].
      destruct Hsp as (S1 & S2 & S3). repeat split; [lia | exact S2].
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity | intros; reflexivity].
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) intros HH. discriminate HH.
    - (* [comment removed for export] *)
      constructor.
    - (* [comment removed for export] *)
      replace (m_kernel model0) with (in_kernel inp) by reflexivity.
      replace (vdso_top (m_vmmaps model0)) with VTOP
        by (symmetry; exact (vdso_top_init_model (segments_reserved segs) brk0 mbase sp LIMIT inp)).
      apply incl_appr, incl_refl.
    - (* [comment removed for export] *)
      reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem init_cfg_eq :
    init_config segs apc ph sp brk0 mbase rdraw LIMIT inp = cfg_of segs R0 (a_entry A) FULL0 model0.
  Proof.
    unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp].
    (* [comment removed for export] *)
    unfold FULL0, entryw. rewrite init_mkst. rewrite Hapc. reflexivity.
  Qed.
End Init.
End AsanInitK.
From Stdlib Require FunctionalExtensionality.
Module AsanNodesAuxK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

Lemma reg_neq : forall a b : Z, 0 <= a < 32 -> 0 <= b < 32 -> a <> b -> (Z_to_bv 5 a : bv 5) <> Z_to_bv 5 b.
Proof.
  intros a b Ha Hb Hne Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
  rewrite !Z.mod_small in Heq by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac rif :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?u else ?v] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let c := eval vm_compute in (bv_eqb a b) in
              lazymatch c with
              | true => change (if bv_eqb a b then u else v) with u
              | false => change (if bv_eqb a b then u else v) with v
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
Lemma signed12_0 : bv_signed (0 : bv 12) = 0. Proof. reflexivity. Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma len_eqb_sound : forall SEGS E M k n m,
  know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
  intros SEGS E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
  - apply expr_eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
    cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.

(* [comment removed for export] *)
Lemma kwritable_sound : forall segs E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
  store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
  intros segs E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
  destruct K; try exact (IH Hrest H).
  lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
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
Lemma kimg_cut_sound : forall segs E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros segs E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
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
Lemma reg_lit5 : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof.
  intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma regs_ok_post2 : forall E sr R R' n1 (r1 : bv 5) e1 n2 (r2 : bv 5) e2,
  regs_ok E sr R -> (0 < n1 < 32)%nat -> (0 < n2 < 32)%nat -> n1 <> n2 ->
  bv_unsigned r1 = Z.of_nat n1 -> bv_unsigned r2 = Z.of_nat n2 ->
  getr R' r1 = edenot E e1 -> getr R' r2 = edenot E e2 ->
  (forall r, r <> r1 -> r <> r2 -> getr R' r = getr R r) ->
  regs_ok E (sr_upd (sr_upd sr n1 e1) n2 e2) R'.
Proof.
  intros E sr R R' n1 r1 e1 n2 r2 e2 HR Hn1 Hn2 Hne U1 U2 G1 G2 Gr.
  assert (E1 : r1 = Z_to_bv 5 (Z.of_nat n1)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U1).
  assert (E2 : r2 = Z_to_bv 5 (Z.of_nat n2)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U2).
  pose proof (regs_ok_set_n E _ _ n2 e2 (edenot E e2) (regs_ok_set_n E sr R n1 e1 (edenot E e1) HR Hn1 eq_refl) Hn2 eq_refl) as K.
  rewrite <- E1, <- E2 in K.
  assert (Z1 : r1 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U1 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
  assert (Z2 : r2 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U2 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
  assert (Z12 : r1 <> r2) by (intros H0; apply (f_equal bv_unsigned) in H0; lia).
  intros r. rewrite <- (K r).
  destruct (bv_eqb r r2) eqn:Q2.
  { unfold bv_eqb in Q2. apply Z.eqb_eq in Q2. apply bv_eq in Q2. subst r. rewrite getr_same by exact Z2. exact G2. }
  assert (N2 : r <> r2) by (intros ->; rewrite bv_eqb_refl in Q2; discriminate).
  rewrite (getr_other _ r2 _ r N2).
  destruct (bv_eqb r r1) eqn:Q1.
  { unfold bv_eqb in Q1. apply Z.eqb_eq in Q1. apply bv_eq in Q1. subst r. rewrite getr_same by exact Z1. exact G1. }
  assert (N1 : r <> r1) by (intros ->; rewrite bv_eqb_refl in Q1; discriminate).
  rewrite (getr_other _ r1 _ r N1). apply Gr; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint nb_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt b a && nb_lt b c
  | EExt _ _ _ a => nb_lt b a
  | EBlob _ _ _ _ => false
  end.

Lemma edenot_ev_agree : forall b E E' e,
  nb_lt b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
  intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
  - apply Hag. apply Nat.ltb_lt. exact H.
  - rewrite (IHe H Hag). reflexivity.
  - discriminate.
Qed.

(* [comment removed for export] *)
Lemma fetch_lit : forall segs z (w : word) x,
  bv_unsigned w = z -> fetch_word segs w = Some x -> fetch_word segs (Z_to_bv 64 z) = Some x.
Proof.
  intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
  apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma with_ss_idem : forall cs s1 s2, with_ss (with_ss cs s1) s2 = with_ss cs s2.
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : forall cs s, a_ss (with_ss cs s) = s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_le' : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
                                       /\ bv_unsigned a < bv_unsigned (page_base a) + 4096
                                       /\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
  intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma page_in_ranges_bounds' : forall (a : word) l lo hi,
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l ->
  page_in_ranges (page_base a) l = true ->
  lo <= bv_unsigned a /\ bv_unsigned a + 1 <= hi + 4095.
Proof.
  intros a l lo hi Hl Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) Hl iv Hin) as [L1 L2].
  pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. lia.
Qed.

Lemma A_wf_allowA' : forall A E cs, A_wf (allowA A E cs).
Proof.
  intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
  apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
  pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
  destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
  - pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
  - pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Section NodesD.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.  (* [comment removed for export] *)
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A E cs model a).

  Lemma Hv_hid : forall E cs model a, Hv E cs model a = true -> hid A argH E cs model a = true.
  Proof. intros E cs model a H. unfold hid, Hv in *. rewrite H. apply orb_true_r. Qed.

  (* [comment removed for export] *)
  Lemma Hv_high : forall E cs model (a : word), utop E <= bv_unsigned a -> Hv E cs model a = false.
  Proof.
    intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
    replace (utop E <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
    rewrite orb_true_r. reflexivity.
  Qed.

  Lemma Hv_hull : forall E cs model (a : word), in_hull A (bv_unsigned a) = true -> Hv E cs model a = false.
  Proof. intros E cs model a Ha. unfold Hv, vis. rewrite Ha. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma page_in_ranges_In' : forall (a : word) l,
    page_in_ranges (page_base a) l = true ->
    exists iv, In iv l /\ bv_unsigned (fst iv) <= bv_unsigned a /\ bv_unsigned a + 1 <= bv_unsigned (fst iv) + bv_unsigned (snd iv)
               /\ bv_unsigned (fst iv) <= bv_unsigned (page_base a) /\ bv_unsigned (page_base a) + 4096 <= bv_unsigned (fst iv) + bv_unsigned (snd iv).
  Proof.
    intros a l Hp. unfold page_in_ranges in Hp. apply existsb_exists in Hp as [iv [Hin Hb]].
    apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (page_base_le' a) as (P1 & P2 & P3). unfold page_size in H2. exists iv. repeat split; try assumption; lia.
  Qed.

  Lemma lazy_cover_vis : forall E cs R FULL model,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> lazy_cover (Hv E cs model) (m_vm_lazy model) (allowA A E cs).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
    apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
    destruct (page_in_ranges_In' w _ Hlz) as (iv0 & Hin0 & B1 & B2 & B3 & B4).
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv0 Hin0) as [L1 L2].
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
    apply orb_prop in Hv0 as [Hv0|Hv0].
    - apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_hull in Hv0. apply andb_prop in Hv0 as [Hv1 Hv0]. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv0. exfalso. lia.
      + apply Z.leb_le in Hv0. exfalso. lia.
    - apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz in Hv0. cbn [negb orb] in Hv0.
      pose proof (page_base_le' w) as (P1 & P2 & P3).
      unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
      + unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      + unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
        apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
        exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
        * apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
        * cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Lemma lazy_cover_hid : forall E cs R FULL model,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> lazy_cover (hid A argH E cs model) (m_vm_lazy model) (allowA A E cs).
  Proof.
    intros E cs R FULL model HC w Hlz Hh. apply (lazy_cover_vis E cs R FULL model HC w Hlz).
    unfold Hv. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hh]. exact Hh.
  Qed.

  Lemma H_off_segments_vis : forall E cs model, H_off_segments SEGS (Hv E cs model).
  Proof.
    intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
    apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
    apply SEGS_in_hull. exact Hh.
  Qed.

  (* [comment removed for export] *)
  Lemma mrestrict_Hv_high : forall E cs model FULL (a : word),
    utop E <= bv_unsigned a -> mrestrict (Hv E cs model) FULL a = FULL a.
  Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma Mr_grows_Hv : forall E cs model FULL,
    mem_grows (Mr A argH E cs model FULL) (mrestrict (Hv E cs model) FULL).
  Proof.
    intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
    destruct (argH E a), (vis A E cs model a); cbn; auto.
  Qed.

  Lemma munrestrict_mrestrict : forall (H : word -> bool) FULL, munrestrict H FULL (mrestrict H FULL) = FULL.
  Proof.
    intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
  Qed.

End NodesD.

End AsanNodesAuxK.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
Module AsanPlanSound2K.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Import AX2K. Import AX2SK. Import APK. Import APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Section Sound2.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

#[local] Notation cs_ok := (APSK.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Lemma kread_bytes_sound : forall E M k n b off zs,
  know_ok SEGS E M k ->
  kread_bytes SEGS n k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat n <= 2 ^ 64 ->
  exists bs, length bs = n /\ map bv_unsigned bs = zs
             /\ forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros E M k n. induction n as [|n IH]; intros b off zs HK Hr Hlo Hhi.
  - cbn in Hr. injection Hr as <-. exists []. repeat split; try reflexivity. intros j Hj. lia.
  - cbn [kread_bytes] in Hr.
    destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes SEGS n k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
    unfold kreadZ in Hz.
    pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as KL.
    destruct (know_lookup SEGS k b off 1 false [] []) as [v scs nx| |]; try discriminate.
    destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hz as <-.
    assert (Hfl : flat E (SA b off) (Z.of_nat 1)) by (unfold flat; change (Z.of_nat 1) with 1; rewrite Nat2Z.inj_succ in Hhi; lia).
    destruct (KL ltac:(constructor) Hfl) as [bs1 (R1 & L1 & V1)].
    destruct bs1 as [|b0 [|? ?]]; try (cbn in L1; lia).
    destruct (IH b (off + 1) rest HK Hrest) as [bs (Lb & Mb & Rb)].
    { unfold estart in *; cbn [a_base a_off] in *. lia. }
    { unfold estart in *; cbn [a_base a_off] in *. rewrite Nat2Z.inj_succ in Hhi. lia. }
    exists (b0 :: bs). split; [cbn; lia|]. split.
    + cbn [map]. rewrite Mb. f_equal.
      cbn [edenot] in V1. apply (f_equal bv_unsigned) in V1. rewrite !u_lit64 in V1.
      unfold extz in V1. cbn [bytes_le_to_Z] in V1. rewrite Z.shiftl_0_l, Z.lor_0_r in V1.
      pose proof (u8_range b0). unfold two64 in *. rewrite Z.mod_small in V1 by lia. exact V1.
    + intros j Hj. destruct j as [|j].
      * cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite <- R1. reflexivity.
      * cbn [nth]. rewrite <- (Rb j) by lia. f_equal. f_equal. unfold estart; cbn [a_base a_off]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_of_bytes1 : forall M n (a : word) bs,
  length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  rdn SEGS M a n = Some bs.
Proof.
  intros M n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
  - destruct bs; [reflexivity | cbn in Hlen; lia].
  - destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
    pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
    destruct n as [|n'].
    + destruct bs'; [exact H0 | cbn in Hlen; lia].
    + apply rdn_cons1; [exact H0|].
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      apply IH; [lia | rewrite Hu1; lia |].
      intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
      exact (Hpt (S j) ltac:(lia)).
Qed.

Theorem node_join_sound : join_stmt SEGS scfg A nx0 LIMIT SINV argH FS0.
Proof.
  intros b off n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_join in Hn.
  destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  rewrite edenot_lit, u64_lit in F2, F3 by lia.
  destruct (kread_bytes_sound E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
  apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
  rewrite (rdn_of_bytes1 _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.
End Sound2.

End AsanPlanSound2K.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0132 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02I45stdpp9bitvector;definitions2bv00K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03I46Stdlib9micromega7EnvRing5PExpr00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8sr_freshC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8fresh_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<maps_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=pairs_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<expr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:fd_vars_ltC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C47Corelib4Init9Datatypes4andbC49OSSVerify5KrLib:AxSymRun3K9env_agreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9ext_call2C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;after_call2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK7kept_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_updC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init9Datatypes9andb_propC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@w_fresh_ok_partsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?ext_call2_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib>AsanPlanSoundK4APSK?sr_vars_lt_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@sr_vars_lt_freshC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK8ext_callC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAext_call2_agree16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKAexpr_vars_lt_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>sr_vars_lt_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_regsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?regs_after_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>regs_ok_agree'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7regs_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>w_env_agree_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9call_coreC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7with_ssC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z7inj_addC49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3NCSC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<caller_savedC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK>asanreflect_fxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00C46Stdlib5Lists4List2Inc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=nth_repeat_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKDfirstn_skipn_map_nthC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List7map_extC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega7EnvRing5PExpr07C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib7Mh_00385Hoare3at_C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC46Stdlib9micromega;ZifyClasses9and_morphC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4a_ssC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK<node_smearvaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6set_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7with_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4s_pcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6alwaysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK:xn_smearvaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z3ltbC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3acs01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eqb_eqC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xlo_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xhi_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9reg_soundC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK2HvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02C59OSSVerify5KrLib7Mh_00385Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib7Mh_00368AsanAcct=restrict_mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKBH_off_segments_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK>lazy_cover_visC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<A_wf_allowA'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_haltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib>AsanPlanSoundK4APSK>env_agree_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00C49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:edenot_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=regs_ok_set_nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK@regs_ok_transferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<with_ss_idemC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<a_ss_with_ssC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKEmunrestrict_mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:node1_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7set_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5mk_ssC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK<smearva_valsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK>asanreflect_fxC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9sym_state00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega:ZMicromega;ZArithProof01I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sentry00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~".
Module AsanPlanSoundSumsK.
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
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPopFree.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanPlanSoundSumsK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4ridxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205K45stdpp9bitvector;definitions2bv01C47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7regs_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00C46Stdlib5Lists4List2InK46Stdlib9micromega6VarMap1t01K46Stdlib5Lists4List5NoDup01I46Stdlib5Lists4List5NoDup00K46Stdlib5Lists4List5NoDup02C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<caller_savedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8sr_freshC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_updC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_specI47Corelib4Init9Datatypes7reflect00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:nth_sr_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC47Corelib4Init5Peano2ltC47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib5Arith8PeanoNat3Nat8eqb_reflc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@nth_sr_fresh_outC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses6mkapp2C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2evC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK8ext_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2ebC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat8leb_specI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init9Datatypes4andbC47Corelib4Init3Nat3subK47Corelib4Init5Logic3and01C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3NCSC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6leb_leC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init9Datatypes?andb_true_introC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC46Stdlib5Lists4List6in_decC46Stdlib5Lists4List6In_nthI47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK7kept_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>ext_call_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:AxSymRun3K9env_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?nth_sr_vars_lt'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=edenot_agree'C1?~~~~~~~~~~~~~~~I47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:ridx_rangeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;reg_of_ridxC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<ext_call_varC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?nth_sr_fresh_inC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAregs_ok_pointwiseC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat6eq_decc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKBcaller_saved_nodupC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec8Z_lt_decC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:wbytes_outC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith4Znat5Z2Nat2idC47Corelib7Classes?RelationClasses=eq_TransitiveK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:wbytes_nthC1?~~~~~~~~~~~~~~~C46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK46Stdlib9micromega5Tauto8GFormula07C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z7add_0_rC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_addC49OSSVerify5KrLib8PropExec6u_add1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List9seq_shiftC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1ZAmul_pow2_bits_lowC46Stdlib4Bool4Bool<andb_false_rC49OSSVerify5KrLib8PropExec>Z_testbit_highC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6bits_0C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4lxorc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAland_shl_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z@add_nocarry_lxorC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z8lxor_lorC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC49OSSVerify5KrLib8PropExecDbytes_le_to_Z_nonnegC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@lor_shl_disjointC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8lor_commC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z6shiftrC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKFZ_to_le_bytes_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKIword_to_le_bytes_of_bytesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5a_offC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kwritableC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry07C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK5elenZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8expr_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;expr_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xlo_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK=xinside_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry09C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry0:C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K7xinsideC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5two64C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;kwritable_xC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xhiC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xhi_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7kzero_xC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List?Forall_flat_mapC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kimg_cut1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C47Corelib4Init9Datatypes3appC46Stdlib4Bool4Bool=orb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC46Stdlib5Lists4List:Forall_appK47Corelib5Lists7ListDef6Forall01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8kimg_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:Forall_oneC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K;know_lookupC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKAknow_lookup_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK8sc_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK8piece_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9adenot_SAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4extzC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8sidecond00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7kread8eC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<lookup_pieceC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6kreadZC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z<pos_div_euclC56Stdlib6ZArith6BinInt1Z3oppC49OSSVerify5KrLib8PropExec?bytes_le_singleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_lit64C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions=bv_wrap_smallK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr08C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;kread_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<kreadZ1_byteC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions?bv_add_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec7rdn_appC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K>zbytes_le_to_ZC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef:Forall_indC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:zbytes_mapC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List;firstn_all2C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:copy_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC46Stdlib5Lists4List9app_nil_rC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List:firstn_appC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9rdn_skipnC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List:skipn_all2C46Stdlib5Lists4List9skipn_appc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=kread8e_pieceC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAkread_bytes_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?zbytes_of_smallC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9reg_soundC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7reg_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=reg_lit_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9split_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK?split_lit_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=know_ok_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6flat_xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<flat_x_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8fresh_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=pairs_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9hid_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_frameC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=lazy_cover_csC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6spiece00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;A_wf_allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKAH_off_segments_csC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>fresh_ok_partsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_readableC56Stdlib6NArith6BinNat1N6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBsegment_read_bytesc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?find_segment_InC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4to_Nc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9wview_rd1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7with_ssC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@w_fresh_ok_partsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<maps_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_fdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKCw_H_off_segments_csC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?w_lazy_cover_csC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=w_A_wf_allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_haltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct=restrict_mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=w_cs_ok_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;w_hid_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<allowA_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKKmrestrict_munrestrict_cleanC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=w_cs_ok_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:fd_vars_ltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK>asanreflect_fxC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC59OSSVerify5KrLib>AsanPlanSoundK4APSK>sr_vars_lt_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:after_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?regs_after_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>know_ok_agree'C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>w_env_agree_leC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9call_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8ext_listC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>ext_list_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9ext_call2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;ext_list_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7ret_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3regC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;w_reg_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop04K4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop06K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5aluop08K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop0:C46Stdlib5Lists4List9nth_indepC46Stdlib5Lists4List7map_nthC46Stdlib5Lists4List7seq_nthC46Stdlib5Lists4List:length_seqc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;nth_map_seqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=nth_repeat_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;off_image_xC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>kimg_cut_soundC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z7mod_modc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9fill_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6alwaysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<summary_fillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK@summary_fill_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?summary_fill_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8kn_havocC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=ret_lit_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?w_reg_lit_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAw_split_lit_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?call_node_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAkwritable_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=kzero_x_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<Z_to_bv8_modC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;wbytes_sameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK8k0_soundC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?w_know_ok_havocC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula02c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>wbytes_fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:node1_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula0:K46Stdlib9micromega5Tauto4kind02C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_allC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;x_memiszeroC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK8miz_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;summary_mizC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?summary_miz_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK>summary_miz_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K>ranges_apart_xC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5eaddzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkAluC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkAlu_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?kwritable_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKDranges_apart_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<rdn1_overlayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4findC46Stdlib5Lists4List<length_skipnc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9copy_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<summary_copyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK@summary_copy_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?summary_copy_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;after_call2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<kblob_prefixC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>split_lit_varsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>w_flat_x_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<store_ok_rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?ext_call2_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List6in_seqC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List=length_firstnc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKKword_to_le_bytes_of_bytes_nC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<ext_call2_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:edenot_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK7rdn_nthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idK46Stdlib9micromega5Tauto8GFormula01c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>wbytes_definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKDknow_ok_unk_intro_ptC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@call_node_sound2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK?rdn_overlay_allC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6zlit64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9zlit64_eqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK@copy_facts_soundC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison01K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7img_covC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>existsb_existsC47Corelib7Classes?RelationClasses;reflexivityC47Corelib7Classes?RelationClassesBPreOrder_Reflexivec69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<SEALED_BYTESC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8SEALED_WC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat;le_preorderC46Stdlib5Lists4List8app_nth2C47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC56Stdlib6ZArith4Znat5Nat2Z6inj_geK46Stdlib9micromega=RingMicromega3Op204C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:x_istrncpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8x_sealedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=istrncpy_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK@summary_istrncpyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APKDsummary_istrncpy_refC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APKCsummary_istrncpy_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9elenZ_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=img_cov_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK:rdn_of_nthC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKCSEALED_BYTES_nth_hiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKCSEALED_BYTES_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6u_lit0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK>SEALED_W_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_extC46Stdlib5Lists4List9nth_skipnC46Stdlib5Lists4List;skipn_skipnc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKDfirstn_skipn_map_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib7Mh_0112;AsanPopFree8pf_bytesC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02C59OSSVerify5KrLib7Mh_0112;AsanPopFree?pf_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0112;AsanPopFree=pf_bytes_cellC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0112;AsanPopFreeCword_to_le_bytes4_ZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=popfree_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9x_popfreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0112;AsanPopFree<popfree_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK?summary_popfreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK2pcC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3addC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4a_ssC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3subC57Corelib7BinNums6IntDef1Z3mulC57Corelib7BinNums6IntDef1Z3divC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3regC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z3oppC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5eaddzC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z6to_natC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK=popfree_factsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8kn_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7with_ssC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z7mod_addC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>env_agree_reflC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC56Stdlib5Arith8PeanoNat3Nat6eqb_eqC56Stdlib5Arith8PeanoNat3Nat7eqb_neqc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKCpopfree_facts_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK@Forall_app_introC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3acs00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9x_imemsetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKBsummary_fill_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6x_stmtC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8x_memsetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9x_imemcpyC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKBsummary_copy_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8x_memcpyC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode04C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKAsummary_miz_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode05C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKFsummary_istrncpy_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode09C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKEsummary_popfree_soundC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode0:C1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module APSXK.
Import AX2K. Import AX2SK. Import APK. Import APSK.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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

Lemma nth_sr_vars_lt' : forall b sr r, APK.sr_vars_lt b sr = true -> (r < 32)%nat -> APK.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [APK.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> APK.sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => APK.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
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
  pose proof (AX2SK.bytes_le_to_Z_bound bs) as Hb.
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
    (* [comment removed for export] *)
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
Variable rz : Z.        (* [comment removed for export] *)
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
(* [comment removed for export] *)
Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.  (* [comment removed for export] *)
Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.                                                              (* [comment removed for export] *)
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
  APK.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ APK.kn_vars_lt (nxt cs) (kn cs) = true
  /\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
  /\ APK.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
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
  APK.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> APK.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
  induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
  apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [APK.expr_vars_lt]. apply Nat.ltb_lt. lia.
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
  assert (Hsf : APK.sr_vars_lt (nxt cs + NCS) sr1 = true).
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


Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> APK.expr_vars_lt m e = true -> APK.expr_vars_lt m b = true.
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [APK.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
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
            APK.kn_vars_lt (nxt cs) (kn cs) = true /\ APK.expr_vars_lt (nxt cs) db = true /\ APK.expr_vars_lt (nxt cs) ne = true
            /\ APK.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
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
  intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := MR E cs model FULL) in *.
  unfold summary_popfree in Hn.
  destruct (Z.eqb (pc cs) (x_popfree A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct args as [|[K| | | | | | |] [|]]; try discriminate.
  destruct (reg_lit cs 10) as [i|] eqn:H10; [|discriminate].
  destruct (reg_lit cs 12) as [c|] eqn:H12; [|discriminate].
  destruct (reg_lit cs 21) as [s|] eqn:H21; [|discriminate].
  destruct (reg_lit cs 19) as [n|] eqn:H19; [|discriminate].
  destruct (split_lit (eaddz (reg cs 11) (- (4 * n)))) as [lb lk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 11)) as [el|] eqn:Hel; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [eh|] eqn:Heh; [|discriminate].
  match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
  repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
  apply Z.leb_le in Hcond.
  repeat match goal with
         | Hl : Z.leb _ _ = true |- _ => apply Z.leb_le in Hl
         | Hl : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hl end.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  match goal with Hl : fresh_ok nx0 cs = true |- _ => rename Hl into Hfresh end.
  match goal with Hl : kwritable_x _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
  match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.
  (* [comment removed for export] *)
  destruct (w_reg_lit_sound E cs R FULL model 10 _ HC ltac:(lia) H10) as [R10 Hi].
  destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 Hc].
  destruct (w_reg_lit_sound E cs R FULL model 21 _ HC ltac:(lia) H21) as [R21 Hs].
  destruct (w_reg_lit_sound E cs R FULL model 19 _ HC ltac:(lia) H19) as [R19 Hnn].
  pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hel) as Hel'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh'.
  repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
  set (ew := edenot E (reg cs 11)) in *. set (e := bv_unsigned ew) in *.
  pose proof (u64_range ew) as Her. fold e in Her.
  set (cnt := n - i) in *.
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite elenZ_lit in Wst, Whi by lia.
  set (D := estart E (SA lb lk)) in *.
  pose proof (w_split_lit_denot E _ lb lk Hspl) as Hsd.
  assert (HloD : edenot E (eaddz (reg cs 11) (- (4 * n))) = Z_to_bv 64 (e - 4 * n)).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64. fold ew. rewrite u_lit64. unfold two64.
    rewrite u64_lit by lia. fold e.
    replace (e + - (4 * n) mod 2 ^ 64) with ((e - 4 * n) + 1 * 2 ^ 64).
    2: { rewrite <- (Z.mod_add (- (4 * n)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  assert (HD : D = e - 4 * n).
  { assert (HDdef : D = bv_unsigned (edenot E lb) + lk) by reflexivity.
    rewrite HloD, <- HDdef in Hsd. apply (f_equal bv_unsigned) in Hsd. rewrite !u64_lit in Hsd by lia. lia. }
  destruct (SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(rewrite <- HD; apply Wst; lia)) as (regs' & Hms & G10 & G12 & G14 & G15 & Gkeep).
  set (M' := wbytes M (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) in *.
  eapply (call_core cs E E R FULL model T (pc cs + 32) _ _ (nxt cs) regs' M' HC Hfresh (env_agree_refl _ _)).
  (* [comment removed for export] *)
  4: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r) as HR. unfold sr_get in HR.
    assert (Hrz : bv_eqb r 0%bv = false).
    { unfold bv_eqb. apply Z.eqb_neq. intros Hc0. apply Hr0. apply bv_eq. exact Hc0. }
    rewrite Hrz in HR.
    destruct (Nat.eqb (ridx r) 15) eqn:E15.
    { apply Nat.eqb_eq in E15. rewrite (reg_of_ridx r 15 E15). refine (eq_trans G15 _). rewrite HloD. reflexivity. }
    destruct (Nat.eqb (ridx r) 14) eqn:E14.
    { apply Nat.eqb_eq in E14. rewrite (reg_of_ridx r 14 E14). refine (eq_trans G14 _). cbn [edenot]. f_equal; f_equal; lia. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12.
    { apply Nat.eqb_eq in E12. rewrite (reg_of_ridx r 12 E12). refine (eq_trans G12 _). cbn [edenot]. f_equal; lia. }
    destruct (Nat.eqb (ridx r) 10) eqn:E10.
    { apply Nat.eqb_eq in E10. rewrite (reg_of_ridx r 10 E10). refine (eq_trans G10 _). reflexivity. }
    apply Nat.eqb_neq in E15. apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E10.
    rewrite Gkeep; [exact HR| | | |]; intros Hrr; [apply E10 | apply E12 | apply E14 | apply E15]; rewrite Hrr; reflexivity.
  - (* [comment removed for export] *)
    assert (Hlen : length (pf_bytes c s (Z.to_nat (n - i))) = (4 * Z.to_nat cnt)%nat) by (unfold cnt; apply pf_bytes_length).
    assert (Hbase : bv_unsigned (Z_to_bv 64 (e - 4 * n)) = D) by (rewrite HD; apply u64_lit; lia).
    unfold know_ok. apply Forall_app_intro; [|apply Forall_app_intro].
    + fold cnt. apply (popfree_facts_sound E M lb lk cnt c s (Z.to_nat K) (Z_to_bv 64 (e - 4 * n)) Hbase); lia.
    + destruct (Z.ltb K cnt) eqn:HKc; [|constructor]. apply Z.ltb_lt in HKc.
      constructor; [|constructor]. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [unfold flat; lia|].
      intros q Hq. fold D. replace (D + q) with (bv_unsigned (Z_to_bv 64 (e - 4 * n)) + Z.of_nat (Z.to_nat q)) by lia.
      subst M'. apply wbytes_defined; rewrite Hlen; lia.
    + eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
      intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite Hlen; lia.
Qed.

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

End APSXK.
End AsanPlanSoundSumsK.
Module AsanNodesExtraK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanPlanSound2K.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanNodesAuxK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanPlanSoundSumsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanNodesExtraDefsK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanNodesExtraK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3sndC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=nth_repeat_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List7map_mapc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKDfirstn_skipn_map_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib5Lists7ListDef6firstnC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List7map_extC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK=node_absbytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8fresh_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib5Arith8PeanoNat3Nat3lebC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K;kn_readableC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK9kwritableC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init5Logic2eq01C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3nxtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK<expr_vars_ltC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3nxtC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4bumpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3acs01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6set_knC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat6leb_leC59OSSVerify5KrLib>AsanPlanSoundK4APSK>fresh_ok_partsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<maps_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_fdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4flatC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKAkn_readable_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK?kwritable_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6estartC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6adenotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6flat_uC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK<store_ok_rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC59OSSVerify5KrLib>AsanPlanSoundK4APSK4ext1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:ext1_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:AxSymRun3K9env_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_agreeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<env_agree_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKCbytes_le_to_Z_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_lit64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mk_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry01C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_1_rC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_knowC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4bumpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6set_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7regs_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5s_logC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib>AsanPlanSoundK4APSK6fds_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC59OSSVerify5KrLib>AsanPlanSoundK4APSK:maps_matchC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib>AsanPlanSoundK4APSK7hole_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK4seps00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4utopC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC59OSSVerify5KrLib>AsanPlanSoundK4APSK6in_ivsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8amap_denC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7am_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6am_lenC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC59OSSVerify5KrLib>AsanPlanSoundK4APSK9sum_sizesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8pagedownC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK8in_ghostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3RNAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3RLZC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2evC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3eqbC56Stdlib5Arith8PeanoNat3Nat8eqb_reflC59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9hid_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:AxSymRun3K<adenot_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib:AxSymRun3K:flat_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesc59OSSVerify5KrLib7Mh_0132?AsanPlanSound2KBZ_to_le_bytes_to_ZC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib>AsanPlanSoundK4APSK<cs_ok_set_knC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes4andbK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=pairs_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:fd_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<expr_vars_ltC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3acs00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5two64C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sentry00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mkind02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_sppgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7PID_MAXC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib5Lists4List2hdC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib>AsanPlanSoundK4APSK6alwaysC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK;xn_absbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebc59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK>absbytes_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:node1_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_getC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib4Init5Logic3notC59OSSVerify5KrLib>AsanPlanSoundK4APSK8ext_listC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8sr_freshC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK@regs_ok_transferC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffC69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_updC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>regs_ok_agree'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7ext1_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK=regs_ok_set_nC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib>AsanPlanSoundK4APSK?sr_vars_lt_monoC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC59OSSVerify5KrLib>AsanPlanSoundK4APSK>sr_vars_lt_updC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC49OSSVerify5KrLib8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:node_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8fresh_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7with_ssC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>ext_list_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_regsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List>forallb_forallc59OSSVerify5KrLib7Mh_0132?AsanNodesExtraKEregs_ok_sr_fresh_clobC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK8aim_cellC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6kreadZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKAknow_lookup_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4extzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9estart_SAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK8sc_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK9adenot_SAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K;know_lookupC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K8sidecond00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4lres03C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK2HvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSKAH_off_segments_csC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;rdn_visibleC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK6Hv_hidC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK>xn_addrisinmemC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK@node_addrisinmemC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9split_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK3regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K:base_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK9aim_entryC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K<ranges_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK8aim_got1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK6aim_g1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK8aim_got2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK6aim_g2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK8aim_got3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK6aim_g3C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK6set_pcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7set_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9reg_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK@base_range_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:u_of_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SKBranges_apart_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK>aim_cell_soundC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injc59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK9rdn_Mr_HvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib7Mh_00385Hoare:regs_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct=restrict_mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_haltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkAluC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7mod_addC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:edenot_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkAlu_denotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6or_indK47Corelib4Init5Logic2or02c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK@havoc_clob_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKBH_off_segments_visC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK>lazy_cover_visC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<A_wf_allowA'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allow1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8flat_mapC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib>AsanPlanSoundK4APSK<allowA_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKEmunrestrict_mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK4eaddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK5eaddzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK7set_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK:node_havocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4eaddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5eaddzC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses6mkapp2C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC59OSSVerify5KrLib7Mh_0076CAsanNodesExtraDefsK8aim_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK>asanreflect_fxC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib7Mh_0132?AsanNodesExtraK8aim_clobC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBuf".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition aim_clob : list (bv 5) := [5; 6; 7; 11; 14; 15; 16; 17; 28]%bv.
Definition aim_spec (SEGS : list Segment) (prm : aim_params) : Prop :=
  forall (mem rom : word -> option byte) (regs : bvmap 5 word) (a sz : word) (bs1 bs2 bs3 bs4 bs5 bs6 : list byte),
  getr regs 10 = a -> getr regs 11 = sz ->
  getr regs 9 = Z_to_bv 64 0x7fff8000 -> getr regs 14 = Z_to_bv 64 0x7fff7fff ->
  rdn SEGS mem (Z_to_bv 64 (aim_got1 prm)) 8 = Some bs1 -> bytes_le_to_Z bs1 = aim_g1 prm ->
  rdn SEGS mem (Z_to_bv 64 (aim_got2 prm)) 8 = Some bs2 -> bytes_le_to_Z bs2 = aim_g2 prm ->
  rdn SEGS mem (Z_to_bv 64 (aim_got3 prm)) 8 = Some bs3 -> bytes_le_to_Z bs3 = aim_g3 prm ->
  rdn SEGS mem (Z_to_bv 64 (aim_g1 prm)) 8 = Some bs4 -> bytes_le_to_Z bs4 = 0%Z ->
  rdn SEGS mem (Z_to_bv 64 (aim_g2 prm)) 8 = Some bs5 -> bytes_le_to_Z bs5 = 0%Z ->
  rdn SEGS mem (Z_to_bv 64 (aim_g3 prm)) 8 = Some bs6 -> bytes_le_to_Z bs6 = (2^47 - 1)%Z ->
  (8 <= bv_unsigned sz)%Z -> (bv_unsigned sz mod 8 = 0)%Z ->
  ((bv_unsigned a + bv_unsigned sz <= 0x7fff7000)%Z
   \/ (0x10007fff8000 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned sz <= 2^47)%Z) ->
  exists regs',
    msteps SEGS (mkst regs (Z_to_bv 64 (aim_entry prm)) mem rom) (mkst regs' (Z_to_bv 64 (aim_entry prm + 0x22c)) mem rom)
    /\ getr regs' 11 = Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - 8)
    /\ regs_agree (fun r => In r aim_clob) regs regs'.


Section NodesX.
  Variable SEGS : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
  Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* [comment removed for export] *)
  Hypothesis SEGS_wr : APSXK.segs_wr_ok SEGS.

  #[local] Notation Hv := (AsanNodesAuxK.Hv A).
  #[local] Notation lazy_cover_vis := (AsanNodesAuxK.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (AsanNodesAuxK.H_off_segments_vis SEGS A SEGS_in_hull).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma absbytes_sound : forall E cs R FULL model b off n cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_absbytes SEGS nx0 cs b off n = Some cs' ->
    exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R FULL model /\ pc cs' = pc cs.
  Proof.
    intros E cs R FULL model b off n cs' HC H. unfold node_absbytes in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection H as <-.
    apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hn8]. apply andb_prop in Hc as [Hc Hn1]. apply andb_prop in Hc as [Hfr Hvb].
    apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8.
    destruct (fresh_ok_parts nx0 cs Hfr) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    assert (RD : flat E (SA b off) (Z.of_nat n) /\ exists bs, rdn SEGS (Mr A argH E cs model FULL) (adenot E (SA b off)) n = Some bs /\ length bs = n).
    { apply orb_prop in Hrd as [Hrd|Hwr].
      - exact (kn_readable_sound SEGS E _ (kn cs) _ (kn cs) b off n HK HK Hn1 Hn8 Hrd).
      - destruct (AsanNodesAuxK.kwritable_sound SEGS E _ (kn cs) (kn cs) b off (Z.of_nat n) HK HK Hwr ltac:(lia)) as (Hst & B1 & B2).
        assert (Hfl : flat E (SA b off) (Z.of_nat n)) by (unfold flat; lia).
        split; [exact Hfl|]. rewrite Nat2Z.id in Hst.
        assert (Ea : adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off))) by (apply bv_eq; rewrite (flat_u E _ _ Hfl), u64_lit; unfold two64; lia).
        rewrite Ea. apply (APSXK.store_ok_rdn SEGS SEGS_wr); [rewrite u64_lit; unfold two64; lia | exact Hst]. }
    destruct RD as [Hfl (bs & Hrd' & Hlen)].
    set (w := Z_to_bv 64 (bytes_le_to_Z bs)).
    set (v := nxt cs). set (E' := ext1 E v w).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfr HC) as HC'.
    exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
    pose proof (bytes_le_to_Z_bound bs) as Hbnd. rewrite Hlen in Hbnd.
    assert (Hw : bv_unsigned w = bytes_le_to_Z bs).
    { unfold w. rewrite u_lit64. unfold two64. apply Z.mod_small.
      assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
    match goal with |- cs_ok _ _ _ _ _ _ E' ?csx R FULL model =>
      replace csx with (set_kn (bump cs 1) (KWord (SA b off) n (EVar v) :: KRange (EVar v) 0 (2 ^ (8 * Z.of_nat n) - 1) :: kn cs))
        by (unfold set_kn, bump, with_ss; cbn; rewrite Nat.add_1_r; reflexivity) end.
    apply cs_ok_set_kn.
    - destruct HC'; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz];
        try assumption; reflexivity.
    - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. change (Mr A argH E' (bump cs 1) model FULL) with (Mr A argH E' cs model FULL).
      assert (Hv : edenot E' (EVar v) = w) by (cbn [edenot ev E' ext1]; rewrite Nat.eqb_refl; reflexivity).
      assert (HMr : Mr A argH E' cs model FULL = Mr A argH E cs model FULL).
      { unfold Mr. rewrite (hid_agree A nx0 argH e_sp0_init argH_agree v E E' cs model Hag Fle Fallow). reflexivity. }
      assert (Had : adenot E' (SA b off) = adenot E (SA b off)).
      { symmetry. eapply (adenot_agree v); [exact Hag | exact Hvb]. }
      constructor; [| constructor; [| exact HK']].
      + cbn [kentry_ok]. split; [exact Hn8|]. split.
        * apply (proj1 (flat_agree v E E' (SA b off) (Z.of_nat n) Hag Hvb)). exact Hfl.
        * rewrite HMr, Had, Hrd', Hv. f_equal. unfold word_to_le_bytes. rewrite Hw, <- Hlen. symmetry. apply Z_to_le_bytes_to_Z.
      + cbn [kentry_ok]. rewrite Hv, Hw. lia.
  Qed.

  Theorem xn_absbytes_sound : forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (xn_absbytes SEGS nx0 args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_absbytes in Hn.
    destruct args as [|b [|[zo| | | | | | |] [|[zn| | | | | | |] [|]]]]; try discriminate.
    destruct (Z.leb 0 zn); [|discriminate].
    destruct (absbytes_sound E cs R FULL model b zo (Z.to_nat zn) cs' HC Hn) as (E' & Hag & HC1 & Hpc).
    rewrite <- Hpc. exact (Hk E' R FULL model Hag HC1 eq_refl).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[local] Notation munrestrict_mrestrict := (AsanNodesAuxK.munrestrict_mrestrict).

  Lemma regs_ok_transfer : forall E sr R1 R2,
    (forall r, getr R2 r = getr R1 r) -> regs_ok E sr R1 -> regs_ok E sr R2.
  Proof. intros E sr R1 R2 Heq HR r. rewrite Heq. apply HR. Qed.

  Section Smear.
    (* [comment removed for export] *)
    Variable mbase : word.
    Hypothesis SMEAR : forall (mem rom : word -> option byte) regs (x : word),
      getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
      exists regs',
        msteps SEGS (mkst regs (at_ mbase 0) mem rom) (mkst regs' (at_ mbase 180) mem rom)
        /\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
        /\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
        /\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
        /\ getr regs' 15 = Z_to_bv 64 9223301668110598144
        /\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.

    Theorem xn_smearva_sound : forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (xn_smearva (bv_unsigned mbase) args).
    Proof.
      intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_smearva in Hn. destruct args; [|discriminate].
      unfold node_smearva in Hn.
      destruct (xlo (kn cs) (reg cs 10)) as [lo|] eqn:Hlo; [|discriminate].
      destruct (xhi (kn cs) (reg cs 10)) as [hi|] eqn:Hhi; [|discriminate].
      match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
      apply andb_prop in Hc as [Hc Hhi']. apply andb_prop in Hc as [Hpc Hlo']. apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo'. apply Z.ltb_lt in Hhi'.
      pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
      pose proof (xlo_sound SEGS E _ (kn cs) (reg cs 10) lo HK Hlo) as L1.
      pose proof (xhi_sound SEGS E _ (kn cs) (reg cs 10) hi HK Hhi) as L2.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
      pose proof (u64_range mbase) as Rmb.
      set (H2 := Hv E cs model).
      set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
      destruct (SMEAR (mrestrict H2 FULL) (seg_rom SEGS) R (getr R 10%bv) eq_refl ltac:(rewrite H10; lia))
        as (R' & Hms & G10 & G11 & G12 & G13 & G14 & G15 & Hag).
      assert (E0 : at_ mbase 0 = Z_to_bv 64 (pc cs)) by (unfold at_; rewrite Hpc, Z.add_0_r; reflexivity).
      assert (E180 : at_ mbase 180 = Z_to_bv 64 (bv_unsigned mbase + 180)) by reflexivity.
      rewrite E0, E180 in Hms.
      unfold cfg_of. fold ms.
      assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (bv_unsigned mbase + 180)) (mrestrict H2 FULL) (seg_rom SEGS))).
      { unfold ms. rewrite restrict_mkst. exact Hms. }
      apply (srz_msteps_restricted_T SEGS scfg H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
               ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
               (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
      intros model' Hinv' Hsame Hclean.
      change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (bv_unsigned mbase + 180)) (mrestrict H2 FULL) (seg_rom SEGS)))
        with (mkst R' (Z_to_bv 64 (bv_unsigned mbase + 180)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
      rewrite munrestrict_mrestrict.
      specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk.
      apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
      unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next].
      eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
      cbn [s_regs].
      (* [comment removed for export] *)
      set (Rc := regupd (regupd (regupd (regupd (regupd (regupd R
                   (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 140737488355327))
                   (Z_to_bv 5 (Z.of_nat 11)) (Z_to_bv 64 18446744073709551615))
                   (Z_to_bv 5 (Z.of_nat 12)) (Z_to_bv 64 3689348814741910323))
                   (Z_to_bv 5 (Z.of_nat 13)) (Z_to_bv 64 1085102592571150095))
                   (Z_to_bv 5 (Z.of_nat 14)) (Z_to_bv 64 72340172838076673))
                   (Z_to_bv 5 (Z.of_nat 15)) (Z_to_bv 64 9223301668110598144)).
      assert (L10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L13 : Z_to_bv 5 (Z.of_nat 13) = (13%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L14 : Z_to_bv 5 (Z.of_nat 14) = (14%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (L15 : Z_to_bv 5 (Z.of_nat 15) = (15%bv : bv 5)) by (apply bv_eq; reflexivity).
      assert (NE : forall a b : bv 5, bv_eqb a b = false -> a <> b) by (intros a b Hab Heq; subst; rewrite bv_eqb_refl in Hab; discriminate).
      apply (regs_ok_transfer E _ Rc R').
      - intros r. unfold Rc. rewrite L10, L11, L12, L13, L14, L15.
        pose proof (Hag r) as HA. cbn [In] in HA.
        destruct (bv_eqb r 15%bv) eqn:E15; [apply bv_eqb_eq in E15; subst r; rewrite G15, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 15%bv _ r (NE _ _ E15)).
        destruct (bv_eqb r 14%bv) eqn:E14; [apply bv_eqb_eq in E14; subst r; rewrite G14, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 14%bv _ r (NE _ _ E14)).
        destruct (bv_eqb r 13%bv) eqn:E13; [apply bv_eqb_eq in E13; subst r; rewrite G13, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 13%bv _ r (NE _ _ E13)).
        destruct (bv_eqb r 12%bv) eqn:E12; [apply bv_eqb_eq in E12; subst r; rewrite G12, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 12%bv _ r (NE _ _ E12)).
        destruct (bv_eqb r 11%bv) eqn:E11; [apply bv_eqb_eq in E11; subst r; rewrite G11, getr_same by (apply NE; reflexivity); reflexivity|].
        rewrite (getr_other _ 11%bv _ r (NE _ _ E11)).
        destruct (bv_eqb r 10%bv) eqn:E10; [apply bv_eqb_eq in E10; subst r; rewrite G10, getr_same by (apply NE; reflexivity); apply bv_eq; reflexivity|].
        rewrite (getr_other _ 10%bv _ r (NE _ _ E10)).
        apply HA. intros [X|[X|[X|[X|[X|[X|[]]]]]]]; subst r;
          first [rewrite bv_eqb_refl in E10 | rewrite bv_eqb_refl in E11 | rewrite bv_eqb_refl in E12
                | rewrite bv_eqb_refl in E13 | rewrite bv_eqb_refl in E14 | rewrite bv_eqb_refl in E15]; discriminate.
      - unfold Rc. cbn [smearva_vals nth].
        repeat (apply regs_ok_set_n; [| lia | rewrite edenot_lit; reflexivity]).
        exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC).
    Qed.
  End Smear.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma regs_ok_sr_fresh_clob : forall rs E sr R R' nx,
    regs_ok E sr R -> APK.sr_vars_lt nx sr = true -> Forall (fun r => 0 < r < 32)%nat rs ->
    (forall q : bv 5, (forall n, In n rs -> q <> Z_to_bv 5 (Z.of_nat n)) -> getr R' q = getr R q) ->
    regs_ok (ext_list E nx (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) rs)) (sr_fresh sr rs nx) R'.
  Proof.
    induction rs as [|r rest IH]; intros E sr R R' nx HR Hsr Hrs Hagr; cbn [sr_fresh map ext_list].
    - apply (regs_ok_transfer E sr R R'); [|exact HR]. intros q. apply Hagr. intros n [].
    - apply Forall_cons_iff in Hrs as [Hr Hrest].
      set (v := getr R' (Z_to_bv 5 (Z.of_nat r))).
      apply (IH (ext1 E nx v) (sr_upd sr r (EVar nx)) (regupd R (Z_to_bv 5 (Z.of_nat r)) v) R' (Datatypes.S nx)).
      + apply regs_ok_set_n; [| exact Hr | apply ext1_at].
        eapply regs_ok_agree'; [apply ext1_agree | exact Hsr | exact HR].
      + apply sr_vars_lt_upd; [eapply sr_vars_lt_mono; [exact Hsr | lia] |]. cbn [APK.expr_vars_lt]. apply Nat.ltb_lt. lia.
      + exact Hrest.
      + intros q Hq.
        assert (NZ : Z_to_bv 5 (Z.of_nat r) <> (0%bv : bv 5)).
        { intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
          change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
          replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
        destruct (bv_eqb q (Z_to_bv 5 (Z.of_nat r))) eqn:Eq.
        * apply (proj1 (bv_eqb_eq _ _)) in Eq. subst q. rewrite getr_same by exact NZ. reflexivity.
        * assert (Hne : q <> Z_to_bv 5 (Z.of_nat r)) by (intros ->; rewrite bv_eqb_refl in Eq; discriminate).
          rewrite (getr_other _ _ _ _ Hne). apply Hagr. intros n [<-|Hn]; [exact Hne | apply Hq; exact Hn].
  Qed.

  Lemma havoc_clob_sound : forall E cs R R' FULL model rs cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_havoc nx0 cs rs = Some cs' ->
    (forall q : bv 5, (forall n, In n rs -> q <> Z_to_bv 5 (Z.of_nat n)) -> getr R' q = getr R q) ->
    exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E')
               /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R' FULL model /\ pc cs' = pc cs /\ kn cs' = kn cs
               /\ a_vis cs' = a_vis cs /\ a_ghost cs' = a_ghost cs.
  Proof.
    intros E cs R R' FULL model rs cs' HC H Hagr. unfold node_havoc in H.
    destruct (fresh_ok nx0 cs && forallb (fun r => Nat.ltb 0 r && Nat.ltb r 32) rs)%bool eqn:Hc; [|discriminate].
    injection H as <-. apply andb_prop in Hc as [Hf Hrs].
    destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := ext_list E (nxt cs) (map (fun r => getr R' (Z_to_bv 5 (Z.of_nat r))) rs)).
    assert (Hag : env_agree (nxt cs) E E') by apply ext_list_agree.
    exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|repeat split; reflexivity].
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hf HC) as HC'.
    destruct HC'; constructor; cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption; [|reflexivity].
    apply (regs_ok_sr_fresh_clob rs E _ R R'); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | exact Fsr | | exact Hagr].
    apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) Hrs r Hr) as Hb.
    apply andb_prop in Hb as [H1 H2]. apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aim_cell_sound : forall E M k c v,
    know_ok SEGS E M k -> aim_cell SEGS k c v = true ->
    exists bs, rdn SEGS M (Z_to_bv 64 c) 8 = Some bs /\ bytes_le_to_Z bs = v.
  Proof.
    intros E M k c v HK H. unfold aim_cell in H. apply andb_prop in H as [H Hz]. apply andb_prop in H as [Hc0 Hc8].
    apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc8. unfold two64 in Hc8.
    unfold kreadZ in Hz.
    destruct (know_lookup SEGS k (ELit 0) c 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
    destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. apply Z.eqb_eq in Hz.
    pose proof (know_lookup_sound SEGS E M k (ELit 0) c 8 false [] [] HK ltac:(lia) ltac:(lia)) as X.
    rewrite HL in X.
    assert (Hst : estart E (SA (ELit 0) c) = c).
    { rewrite estart_SA. cbn [edenot]. rewrite u64_lit by (unfold two64; lia). lia. }
    assert (Hfl : flat E (SA (ELit 0) c) 8) by (unfold flat; rewrite Hst; lia).
    destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
    exists bs. split.
    - rewrite <- Hrd. rewrite APSXK.adenot_SA, Hst. reflexivity.
    - cbn [edenot] in Hv. unfold extz in Hv. apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
      pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with two64 in Hb.
      rewrite (Z.mod_small (bytes_le_to_Z bs)) in Hv by (unfold two64 in *; lia). rewrite Hv. exact Hz.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_Mr_Hv : forall E cs model FULL (a : word) n bs,
    rdn SEGS (Mr A argH E cs model FULL) a n = Some bs -> (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    rdn SEGS (mrestrict (Hv E cs model) FULL) a n = Some bs.
  Proof.
    intros E cs model FULL a n bs Hrd Hnw. rewrite <- Hrd. unfold Mr. apply rdn_ext; [exact Hnw|].
    intros x Hx. pose proof (rdn_visible SEGS _ FULL a n bs (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) Hrd x Hx) as Hh.
    unfold mrestrict. rewrite Hh. destruct (AsanNodesAuxK.Hv A E cs model x) eqn:Ev; [|reflexivity].
    pose proof (AsanNodesAuxK.Hv_hid A argH E cs model x Ev). congruence.
  Qed.

  Section AIM.
    Variable prm : aim_params.
    (* [comment removed for export] *)
    Hypothesis AIMW : aim_spec SEGS prm.

    Theorem xn_addrisinmem_sound : forall args, node1_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 always (xn_addrisinmem SEGS nx0 prm args).
    Proof.
      intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn_addrisinmem in Hn. destruct args; [|discriminate].
      unfold node_addrisinmem in Hn.
      destruct (split_lit (reg cs 10)) as [b off] eqn:Hsp.
      destruct (reg cs 11) as [n| | | | | | |] eqn:R11e; try discriminate.
      destruct (reg cs 9) as [s1| | | | | | |] eqn:R9e; try discriminate.
      destruct (reg cs 14) as [a4| | | | | | |] eqn:R14e; try discriminate.
      destruct (base_range (kn cs) b) as [[lo hi]|] eqn:Hbr; [|discriminate].
      match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
      destruct (node_havoc nx0 (set_reg cs 11 (eaddz (eadd (reg cs 10) (ELit n)) (-8))) aim_regs) as [cs1|] eqn:Hhv; [|discriminate].
      injection Hn as <-.
      apply andb_prop in Hc as [Hc C6]. apply andb_prop in Hc as [Hc C5]. apply andb_prop in Hc as [Hc C4].
      apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [Hc C2]. apply andb_prop in Hc as [Hc C1].
      apply andb_prop in Hc as [Hc Hapart]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo0].
      apply andb_prop in Hc as [Hc Hnal]. apply andb_prop in Hc as [Hc Hn64]. apply andb_prop in Hc as [Hc Hn8].
      apply andb_prop in Hc as [Hc Ha4]. apply andb_prop in Hc as [Hpc Hs1].
      apply Z.eqb_eq in Hpc. apply Z.eqb_eq in Hs1. apply Z.eqb_eq in Ha4. apply Z.leb_le in Hn8. apply Z.ltb_lt in Hn64.
      apply Z.eqb_eq in Hnal. apply Z.leb_le in Hlo0. apply Z.leb_le in Hhi. subst s1 a4. unfold two64 in Hn64.
      pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
      (* [comment removed for export] *)
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as H10.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as H9.
      pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 14 HC ltac:(lia)) as H14.
      rewrite R9e in H9. rewrite R14e in H14. cbn [edenot] in H9, H14.
      replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in H9 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 5 (Z.of_nat 14)) with (14%bv : bv 5) in H14 by (apply bv_eq; reflexivity).
      set (a := getr R 10%bv) in *. set (sz := getr R 11%bv) in *.
      assert (Usz : bv_unsigned sz = n) by (rewrite H11, R11e; cbn [edenot]; apply u64_lit; lia).
      pose proof (base_range_sound SEGS E _ (kn cs) b lo hi HK Hbr) as [B1 B2].
      assert (Hest : estart E (SA b off) = bv_unsigned (edenot E b) + off) by apply estart_SA.
      assert (Ua : bv_unsigned a = estart E (SA b off)).
      { rewrite H10. apply (u_of_split E (reg cs 10) b off Hsp). rewrite Hest. lia. }
      pose proof (ranges_apart_sound SEGS E _ (kn cs) b off n (ELit 0) 0x7fff7000 0x100000001000 HK Hapart) as CASES.
      rewrite (estart_SA E (ELit 0)) in CASES. cbn [edenot] in CASES.
      replace (bv_unsigned (Z_to_bv 64 0)) with 0%Z in CASES by reflexivity.
      assert (Hcase : (bv_unsigned a + bv_unsigned sz <= 0x7fff7000)%Z
                      \/ (0x10007fff8000 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned sz <= 2^47)%Z) by (rewrite Ua, Usz; lia).
      (* [comment removed for export] *)
      set (H2 := Hv E cs model).
      assert (CELL : forall c v, aim_cell SEGS (kn cs) c v = true ->
                exists bs, rdn SEGS (mrestrict H2 FULL) (Z_to_bv 64 c) 8 = Some bs /\ bytes_le_to_Z bs = v).
      { intros c v Hcv. destruct (aim_cell_sound E _ (kn cs) c v HK Hcv) as (bs & Hrd & Hbv).
        exists bs. split; [|exact Hbv]. apply rdn_Mr_Hv; [exact Hrd|].
        unfold aim_cell in Hcv. apply andb_prop in Hcv as [Hcv _]. apply andb_prop in Hcv as [Hc0 Hc8].
        apply Z.leb_le in Hc0. apply Z.ltb_lt in Hc8. unfold two64 in Hc8. rewrite u64_lit by (unfold two64; lia). cbn [Z.of_nat]. lia. }
      destruct (CELL _ _ C1) as (bs1 & RD1 & V1). destruct (CELL _ _ C2) as (bs2 & RD2 & V2). destruct (CELL _ _ C3) as (bs3 & RD3 & V3).
      destruct (CELL _ _ C4) as (bs4 & RD4 & V4). destruct (CELL _ _ C5) as (bs5 & RD5 & V5). destruct (CELL _ _ C6) as (bs6 & RD6 & V6).
      (* [comment removed for export] *)
      set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
      destruct (AIMW (mrestrict H2 FULL) (seg_rom SEGS) R a sz bs1 bs2 bs3 bs4 bs5 bs6 eq_refl eq_refl H9 H14
                  RD1 V1 RD2 V2 RD3 V3 RD4 V4 RD5 V5 RD6 V6 ltac:(lia) ltac:(rewrite Usz; exact Hnal) Hcase)
        as (R' & Hms & G11 & Hagr).
      rewrite <- Hpc in Hms.
      unfold cfg_of. fold ms.
      assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (pc cs + 0x22c)) (mrestrict H2 FULL) (seg_rom SEGS))).
      { unfold ms. rewrite restrict_mkst. exact Hms. }
      pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
      (* [comment removed for export] *)
      set (cs0 := set_reg cs 11 (eaddz (eadd (reg cs 10) (ELit n)) (-8))) in *.
      set (R1 := regupd R (Z_to_bv 5 (Z.of_nat 11)) (getr R' 11%bv)).
      assert (Hv11 : edenot E (eaddz (eadd (reg cs 10) (ELit n)) (-8)) = getr R' 11%bv).
      { rewrite G11. apply bv_eq. unfold eaddz, eadd. rewrite !mkAlu_denot, !edenot_lit.
        rewrite !u_add64. rewrite <- H10. pose proof (u64_range a) as Ra.
        rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
        rewrite (Z.mod_small n) by lia. rewrite (Z.mod_small (bv_unsigned a + n)) by lia.
        replace ((-8) mod 2 ^ 64)%Z with (2 ^ 64 - 8)%Z by reflexivity.
        replace (bv_unsigned a + n + (2 ^ 64 - 8))%Z with ((bv_unsigned a + bv_unsigned sz - 8) + 1 * 2 ^ 64)%Z by lia.
        rewrite Z.mod_add by lia. reflexivity. }
      assert (HC0 : cs_ok SEGS A LIMIT SINV argH FS0 E cs0 R1 FULL model).
      { unfold cs0, set_reg, R1. destruct HC; constructor;
          cbn [with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset a_hna a_hlz]; try assumption; [|reflexivity].
        apply regs_ok_set_n; [assumption | lia | exact Hv11]. }
      assert (Hagr' : forall q : bv 5, (forall m, In m aim_regs -> q <> Z_to_bv 5 (Z.of_nat m)) -> getr R' q = getr R1 q).
      { intros q Hq. unfold R1.
        replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
        destruct (bv_eqb q 11%bv) eqn:E11.
        - apply (proj1 (bv_eqb_eq _ _)) in E11. subst q. rewrite getr_same by (intros HH; discriminate HH). reflexivity.
        - assert (Hne : q <> 11%bv) by (intros ->; rewrite bv_eqb_refl in E11; discriminate).
          rewrite (getr_other _ _ _ _ Hne). apply Hagr. unfold aim_clob. cbn [In].
          intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]; subst q;
            first [ exact (Hne eq_refl)
                  | refine (Hq 5%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 6%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 7%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 14%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 15%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 16%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 17%nat _ _); [cbn; tauto | apply bv_eq; reflexivity]
                  | refine (Hq 28%nat _ _); [cbn; tauto | apply bv_eq; reflexivity] ]. }
      destruct (havoc_clob_sound E cs0 R1 R' FULL model aim_regs cs1 HC0 Hhv Hagr') as (E' & Hag & HC1 & Hpc1 & Hkn1 & Hvis1 & Hgh1).
      (* [comment removed for export] *)
      apply (srz_msteps_restricted_T SEGS scfg H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
               ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
               (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) Hhalt Hms').
      intros model' Hinv' Hsame Hclean.
      change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (pc cs + 0x22c)) (mrestrict H2 FULL) (seg_rom SEGS)))
        with (mkst R' (Z_to_bv 64 (pc cs + 0x22c)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
      rewrite munrestrict_mrestrict.
      assert (Hag2 : env_agree nx0 E E' /\ env_agree (nxt cs) E E') by exact Hag.
      specialize (Hk E' R' FULL model' Hag2).
      unfold cfg_of, set_pc, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. rewrite Hpc.
      apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
      eapply cs_ok_frame; [exact SINV_frame | exact HC1 | exact Hsame | | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) | intros; reflexivity].
      - (* [comment removed for export] *)
        destruct (fresh_ok_parts nx0 cs0 ltac:(unfold node_havoc in Hhv; destruct (fresh_ok nx0 cs0) eqn:Hf0; [reflexivity | discriminate]))
          as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
        replace (allowA A E' cs1) with (allowA A E cs); [exact Hinv'|].
        unfold allowA. rewrite Hvis1, Hgh1. change (flat_map (allow1 A E') (a_vis cs0 ++ a_ghost cs0)) with (allowA A E' cs).
        symmetry. eapply allowA_agree; [exact (proj2 Hag) | exact Fallow].
      - cbn [s_regs]. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC1).
    Qed.
  End AIM.

End NodesX.

End AsanNodesExtraK.
Module AsanNodesIfaceK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK.
Import ListNotations.
Import AX2K. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Nia Cache. Unset Nra Cache. Import AX2SK. Import APK. Import APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable rz : Z.        (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Definition OBL_mmap2 : Prop := forall split : bool, mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmap2 A nx0 LIMIT rz split).   (* [comment removed for export] *)
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT hole).   (* [comment removed for export] *)
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS scfg A nx0 LIMIT SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS scfg A nx0 LIMIT SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS scfg A LIMIT SINV argH FS0.

(* [comment removed for export] *)
Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_sys /\ OBL_exit.

(* [comment removed for export] *)
Lemma OBL_mmap2_unfold :
  OBL_mmap2 <->
  forall split cs csa csb E R FULL model TB,
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model ->
    is_ecall_at SEGS cs = true ->
    node_mmap2 A nx0 LIMIT rz split cs = Some (csa, csb) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg_of SEGS R' (pc csa) FULL' model') TB) ->
    (forall E' R' FULL' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok SEGS A LIMIT SINV argH FS0 E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS scfg (cfg_of SEGS R' (pc csb) FULL' model') TB) ->
    srealizes SEGS scfg (cfg_of SEGS R (pc cs) FULL model) TB.
Proof. unfold OBL_mmap2, mm2_stmt. tauto. Qed.
End Iface.
End AsanNodesIfaceK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.
Module AsanNodesStartXK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanNodesAuxK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.AsanStartLoops OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_AsanNodesStartXK () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List8map_consC47Corelib4Init5Logic6eq_indc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK;nth_map_seqC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib5Lists7ListDef3nthc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXK=nth_repeat_ltC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List7map_mapc69OSSVerify5KrLib7Mh_0132BAsanPlanSoundSumsK5APSXKDfirstn_skipn_map_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib5Lists7ListDef6firstnC35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List7map_extC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Peano2ltK46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00387CatExecBvalid_argv_str_lenC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib5Lists4List2hdC59OSSVerify5KrLib7Mh_00419RefLayout:lay_bsb_nwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec?cat_string_baseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecCtotal_arg_bytes_natC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib7Mh_00387CatExec?cat_struct_sizeC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecEnat_to_word_add_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecCcat_argv_ptr_offsetC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulc59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK6len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK6len_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK6usp_hiC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes6option00C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout<cat_envp_ptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8word_le8C59OSSVerify5KrLib7Mh_00419RefLayout8envp_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout?read_envp_ptr_kC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec>n_to_le_8_specC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK6usp_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout>read_envp_nullC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_00387CatExec7byte_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_00387CatExec@read_argv_byte_kC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK6len_s0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK7STR0_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK6bsb_nwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalI59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6alwaysC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6node_xC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:AxSymRun3K9env_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3nxtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9x_envscanC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2knC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3regC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6escaleC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4eaddC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK;x_envscan_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6set_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_regsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_yloC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_visC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_ghostC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_brkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4a_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_tidsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hnaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5a_hlzC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_sinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2MrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_knowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK=len_eqb_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9reg_soundC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK2HvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;utop_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4utopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKAmrestrict_Hv_highC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK9rd_envp_kC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout?cat_envp_ptr_nzC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK<rd_envp_nullC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib7Mh_0035>AsanStartLoops8env_loopC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0035>AsanStartLoops8env_postC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00368AsanAcct8restrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct=restrict_mkstC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKBH_off_segments_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6allowAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK>lazy_cover_visC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<A_wf_allowA'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_minvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_haltC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct6hcleanC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib>AsanPlanSoundK4APSK>env_agree_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7with_ssC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_knowC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6s_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5mk_ssC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_00385Hoare:regs_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7co_regsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4mkMdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5mkAluC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_mul64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7u_add64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:edenot_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK:mkMd_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK;mkAlu_denotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK=regs_ok_post2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK3hidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<with_ss_idemC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK<a_ss_with_ssC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State7m_pipesC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC59OSSVerify5KrLib7Mh_00368AsanAcctKsame_but_materialized_frameC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinC59OSSVerify5KrLib7Mh_00368AsanAcct;munrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxKEmunrestrict_mrestrictC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0036=AsanAcctShapeGsrz_msteps_restricted_TC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib>AsanPlanSoundK4APSK:node1_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6x_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7len_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7set_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K2evC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem5State6m_timeC59OSSVerify5KrLib7Mh_00368AsanAcct:eager_usedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=m_rlimit_coreC4ELinuxProcessSemantics?LinuxProcessSem5State7m_clockC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_envpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6V_ENVCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK>asanreflect_fxC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_str0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K9sym_state00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K4ELinuxProcessSemantics5Riscv5Instr5mulop01I69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6sentry00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC47Corelib5Lists7ListDef5skipnC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7reg_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8x_pnscanC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5eaddzC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK9kwritableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_loC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6img_hiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8fresh_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:x_pnscan_kC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8kimg_cutC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC59OSSVerify5KrLib>AsanPlanSoundK4APSK7hull_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK7know_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib>AsanPlanSoundK4APSK=reg_lit_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK?kwritable_soundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z7add_0_lc59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK;Mr_grows_HvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib7Mh_00387CatExecAvalid_argv_str_nzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK9rd_str0_jC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0035>AsanStartLoops<cellrel_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0035>AsanStartLoops7pn_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0035>AsanStartLoops7pn_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0035>AsanStartLoops7cellrelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK4ext1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK:ext1_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK>fresh_ok_partsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<maps_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK;cs_ok_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9hid_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<env_agree_leC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8kn_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK<allowA_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7ext1_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132=AsanNodesAuxK>kimg_cut_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK5elenZC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool=orb_false_iffC59OSSVerify5KrLib>AsanPlanSoundK4APSK=know_ok_havocC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propK47Corelib4Init5Logic2or02K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5saddr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK6estartC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK=pairs_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:fd_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK<expr_vars_ltC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib>AsanPlanSoundK4APSK3visC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbK69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode07C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3KHIC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K5two64C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4CEILC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7mul_1_lC59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK8u_sltu64C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K4expr05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6e_str1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6V_ARGCC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8e_argv1wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8kw_argv1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9kentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6adenotC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK:kentry_eqbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3xloC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>existsb_existsC59OSSVerify5KrLib>AsanPlanSoundK4APSK=kentry_eqb_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib>AsanPlanSoundK4APSK>know_ok_filterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6set_knC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK9pc_set_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK@kw_argv1_respellC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib>AsanPlanSoundK4APSK<cs_ok_set_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK<some_inj_acsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xhi_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK<e_argv1w_le1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib@AxSymExec3SoundK5AX2SK9xlo_soundC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0132@AsanNodesStartXK<e_argv1w_ge2C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterI69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K6kentry00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5xnode08C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section NodesD.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.  (* [comment removed for export] *)
  Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.                                                              (* [comment removed for export] *)
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  #[local] Notation Hv := (AsanNodesAuxK.Hv A).
  #[local] Notation lazy_cover_vis := (AsanNodesAuxK.lazy_cover_vis SEGS A LIMIT SINV argH FS0 HULL_ok).
  #[local] Notation H_off_segments_vis := (AsanNodesAuxK.H_off_segments_vis SEGS A SEGS_in_hull).
  #[local] Notation mrestrict_Hv_high := (AsanNodesAuxK.mrestrict_Hv_high A).
  #[local] Notation Mr_grows_Hv := (AsanNodesAuxK.Mr_grows_Hv A argH).

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word SEGS (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word SEGS (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word SEGS (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  (* [comment removed for export] *)
  Variable inp : ProcInput.
  Variable mbase : word.
  Variable entry : word.
  Variable sp : word.
  Variable brk : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv (in_argv inp).
  Hypothesis Hve : valid_envp (in_envp inp).
  Hypothesis Hvl : valid_launch inp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
  Hypothesis Hsp_lo : sp_window_lo <= bv_unsigned sp.
  Hypothesis Hsp_hi : bv_unsigned sp <= sp_window_hi.

  Let argv := in_argv inp.
  Let envp := in_envp inp.
  Let execfn := in_execfn inp.
  Let rseq := kb_rseq (in_kernel inp).
  Let top := ed_top rdraw.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  Let bsb := entry_stack_image inp mbase ph entry sp rdraw.
  (* [comment removed for export] *)
  Let EA := usp + 8 * argc + 16.
  Let STR0 := usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).

  (* [comment removed for export] *)
  Hypothesis SINV_vals : forall E M, SINV E M ->
    uE E e_envp = EA /\ ev E V_ENVC = Z_to_bv 64 envc /\ uE E (e_str0 (rseq_z rseq)) = STR0.
  (* [comment removed for export] *)
  Hypothesis SINV_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Hypothesis SINV_envp : forall E M (a : word), SINV E M ->
    EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem inp mbase ph entry sp rdraw a.
  Hypothesis SINV_str0 : forall E M (a : word), SINV E M ->
    STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem inp mbase ph entry sp rdraw a.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc, argv. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc, envp. destruct Hve as [H _]. lia. Qed.
  Lemma len_s0 : Z.of_nat (length s0) <= 131071.
  Proof. unfold s0, argv. apply (valid_argv_str_len (in_argv inp) 0 Hva). destruct Hva as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. unfold sp_window_lo in Hsp_lo. lia. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. unfold usp. unfold sp_window_hi in Hsp_hi. lia. Qed.
  Lemma bsb_nw : usp + Z.of_nat (length bsb) < 2 ^ 64.
  Proof.
    unfold usp, bsb.
    exact (entry_stack_image_no_wrap Sv48 inp mbase ph entry sp brk rdraw Hlau).
  Qed.

  (* [comment removed for export] *)
  Lemma length_bsb_sum : Z.of_nat (length bsb)
    = Z.of_nat (cat_string_off rseq sp top argv envp execfn)
      + Z.of_nat (launch_string_bytes argv envp execfn) + 8.
  Proof.
    unfold bsb. rewrite entry_stack_image_block, length_build_stack_bytes.
    unfold cat_string_off, rseq, argv, envp, execfn, top.
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma s0_le_strings :
    Z.of_nat (length s0) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn).
  Proof.
    unfold launch_string_bytes, s0, argv, envp, execfn.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
    pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
    destruct (in_argv inp) as [|a t] eqn:Ea.
    - destruct Hva as [[Hc _] _]. cbn in Hc. lia.
    - cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma str0_hi : STR0 + Z.of_nat (length s0) + 9 <= usp + Z.of_nat (length bsb).
  Proof.
    pose proof s0_le_strings. pose proof length_bsb_sum. unfold STR0, usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma str0_ge : usp <= STR0.
  Proof. unfold STR0, usp. lia. Qed.

  Lemma str0_nw : STR0 + Z.of_nat (length s0) + 2 < 2 ^ 64.
  Proof. pose proof str0_hi. pose proof bsb_nw. lia. Qed.

  Lemma STR0_eq :
    cat_argv_ptr (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0
    = Z_to_bv 64 STR0.
  Proof.
    pose proof len_av. pose proof len_ev. pose proof usp_hi. pose proof usp_lo. pose proof bsb_nw.
    unfold STR0, usp, rseq, argv, envp, execfn, top in *.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp) 0)
      by (destruct Hva as [Hl _]; lia).
    change (total_arg_bytes_nat (firstn 0 (in_argv inp))) with 0%nat.
    rewrite (cat_string_base_offset Sv48 inp mbase sp brk rdraw Hlau).
    rewrite nat_to_word_add_merge, word_add_nat. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_envp_k : forall M k, (k < length envp)%nat ->
    (forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem inp mbase ph entry sp rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (cat_envp_ptr top argv envp execfn k)).
  Proof.
    intros M k Hk HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
    assert (Hk' : Z.of_nat k < envc) by (unfold envc; lia).
    rewrite (rdn_ext SEGS 8 M (wrap_mem inp mbase ph entry sp rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA in *; lia | rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia].
      unfold argv, envp, execfn, top.
      rewrite <- n_to_le_8_spec.
      rewrite <- (read_envp_ptr_k SEGS Sv48 inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_hi k Hk).
      f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, argv, envp, usp. lia.
    - rewrite u64_lit; unfold EA in *; [change (Z.of_nat 8) with 8|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold EA in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. lia.
  Qed.

  Lemma rd_envp_null : forall M,
    (forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> M a = wrap_mem inp mbase ph entry sp rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (EA + 8 * Z.of_nat (length envp))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Proof.
    intros M HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi.
    rewrite (rdn_ext SEGS 8 M (wrap_mem inp mbase ph entry sp rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold EA, envc in *; lia | rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia].
      unfold argv, envp, execfn, top.
      rewrite <- n_to_le_8_spec.
      rewrite <- (read_envp_null SEGS Sv48 inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_hi).
      f_equal. rewrite word_add_nat. f_equal. unfold envp_off, EA, argc, argv, envp, usp. lia.
    - rewrite u64_lit; unfold EA, envc in *; [change (Z.of_nat 8) with 8|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold EA, envc in *; lia). change (Z.of_nat 8) with 8 in Ha. apply HM. unfold envc. lia.
  Qed.

  Lemma rd_str0_j : forall M j, (j <= length s0)%nat ->
    (forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M a = wrap_mem inp mbase ph entry sp rdraw a) ->
    rdn SEGS M (Z_to_bv 64 (STR0 + Z.of_nat j)) 1 = Some [byte_at s0 j].
  Proof.
    intros M j Hj HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi. pose proof len_s0.
    pose proof bsb_nw. pose proof str0_hi. pose proof str0_ge. pose proof str0_nw.
    rewrite (rdn_ext SEGS 1 M (wrap_mem inp mbase ph entry sp rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; lia | rewrite u64_lit; [change (Z.of_nat 1) with 1|]; lia].
      unfold byte_at, s0, argv, envp, execfn, top.
      rewrite <- (read_argv_byte_k Sv48 SEGS inp mbase ph entry sp brk rdraw 0 j Hlau ltac:(destruct Hva as [Hl _]; lia) Hj).
      f_equal. rewrite STR0_eq, word_add_nat, u64_lit by lia. reflexivity.
    - rewrite u64_lit; [change (Z.of_nat 1) with 1|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by lia. change (Z.of_nat 1) with 1 in Ha. apply HM. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma envp_ptr_nz : forall k, (k < length envp)%nat ->
    bv_unsigned (cat_envp_ptr top argv envp execfn k) <> 0.
  Proof.
    intros k Hk. unfold argv, envp, execfn, top.
    exact (cat_envp_ptr_nz Sv48 inp mbase ph entry sp brk rdraw Hvl Hlau Hsp_lo Hsp_hi k Hk).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_sound_envscan : x_stmt SEGS scfg A nx0 LIMIT (rseq_z rseq) SINV argH FS0 XEnvScan.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_envscan in Hn.
    destruct (Z.eqb (pc cs) (x_envscan A) && len_eqb (kn cs) (reg cs 9) e_envp)%bool eqn:Hc; [|discriminate].
    injection Hn as <-. apply andb_prop in Hc as [Hpc Heq]. apply Z.eqb_eq in Hpc.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2.
    destruct Xenv as (X1 & X2 & X3). destruct Ee as (Ee1 & Ee2 & Ee3).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 9) e_envp (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Heq) as H9e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as H9.
    replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) in H9 by (apply bv_eq; reflexivity). rewrite H9e in H9.
    assert (H9' : getr R 9%bv = Z_to_bv 64 (EA + 8 * Z.of_nat 0)).
    { rewrite H9. apply bv_eq. rewrite u64_lit by (unfold EA; lia). unfold uE in V1. rewrite V1. lia. }
    (* [comment removed for export] *)
    set (H2 := Hv E cs model).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (HM : forall a : word, EA <= bv_unsigned a < EA + 8 * envc + 8 -> mrestrict H2 FULL a = wrap_mem inp mbase ph entry sp rdraw a).
    { intros a Ha. unfold H2. rewrite mrestrict_Hv_high by (pose proof (APSK.utop_bounds E); rewrite (SINV_sp0 E FULL HS) in *; unfold EA in *; lia). eapply SINV_envp; [exact HS | exact Ha]. }
    destruct (env_loop SEGS (x_envscan A) we1 we2 we3 ltac:(lia) Fe1 Fe2 Fe3 Ee1 Ee2 Ee3 De1 De2 De3
                (mrestrict H2 FULL) (seg_rom SEGS) EA (length envp) (cat_envp_ptr top argv envp execfn)
                ltac:(unfold EA, envc in *; lia)
                ltac:(intros k Kk; split; [apply rd_envp_k; [exact Kk | exact HM] | apply (envp_ptr_nz k Kk)])
                (rd_envp_null _ HM) (length envp) 0%nat R ltac:(lia) H9') as [R' [Hms Hpost]].
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS scfg H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (mrestrict H2 FULL) (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_envscan A + 12)) (munrestrict H2 FULL (mrestrict H2 FULL)) (seg_rom SEGS)).
    rewrite munrestrict_mrestrict.
    specialize (Hk E R' FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [set_pc set_reg with_ss a_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    unfold set_pc, set_reg. rewrite !a_ss_with_ss, !with_ss_idem. cbn [s_regs s_know s_next].
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
    cbn [s_regs]. destruct Hpost as (P9 & P10 & Pag).
    eapply (regs_ok_post2 E _ R R' 9 9%bv _ 10 10%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | lia | lia | reflexivity | reflexivity | | |].
    - rewrite P9. unfold eadd, escale. rewrite !mkAlu_denot, mkMd_denot, !edenot_lit. fold (reg cs 9). rewrite H9e.
      apply bv_eq. rewrite !u_add64, u_mul64, !u64_lit by lia. cbn [edenot]. rewrite V2, u64_lit by lia. unfold uE in V1. rewrite V1.
      rewrite (Z.mod_small (8 * envc)) by lia. rewrite (Z.mod_small (8 * envc + 8)) by lia.
      rewrite Z.mod_small by (unfold EA; lia). unfold envc. lia.
    - rewrite P10. rewrite edenot_lit. reflexivity.
    - intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem x_sound_pnscan : x_stmt SEGS scfg A nx0 LIMIT (rseq_z rseq) SINV argH FS0 XPnScan.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_pnscan in Hn.
    destruct (reg_lit cs 10) as [p|] eqn:Hp10; [|discriminate].
    destruct (reg_lit cs 12) as [c|] eqn:Hp12; [|discriminate].
    destruct c as [|pc|pc]; try discriminate.
    do 6 (destruct pc as [pc|pc|]; try discriminate).
    lazymatch type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [|discriminate] end.
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hc Hlo].
    apply andb_prop in Hc as [Hc Hwr]. apply andb_prop in Hc as [Hpc Heq].
    apply Z.eqb_eq in Hpc. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2. pose proof len_s0 as Ls0.
    pose proof str0_ge as Sge. pose proof str0_nw as Snw. pose proof bsb_nw as Snb. pose proof str0_hi as Shi.
    destruct Xpn as (X1 & X2 & X3). destruct Ep as (Ep0 & Ep1 & Ep2 & Ep3 & Ep4).
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (SINV_vals E FULL HS) as (V1 & V2 & V3).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    (* [comment removed for export] *)
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 p HC ltac:(lia) Hp10) as [H10 Hpr].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in H10 by (apply bv_eq; reflexivity).
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 _ HC ltac:(lia) Hp12) as [H12 _].
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in H12 by (apply bv_eq; reflexivity).
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 11) (eaddz (e_str0 (rseq_z rseq)) 1) HK Heq) as H11e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as H11.
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in H11 by (apply bv_eq; reflexivity). rewrite H11e in H11.
    assert (H11' : getr R 11%bv = Z_to_bv 64 (STR0 + Z.of_nat 0 + 1)).
    { rewrite H11. unfold eaddz. rewrite mkAlu_denot, edenot_lit. apply bv_eq. rewrite u_add64, !u64_lit by lia.
      unfold uE in V3. rewrite V3. rewrite Z.mod_small by lia. lia. }
    (* [comment removed for export] *)
    destruct (kwritable_sound SEGS E _ (kn cs) (kn cs) (ELit 0) p 8 HK HK Hwr ltac:(lia)) as (HKW & _ & _).
    unfold estart in HKW. cbn [a_base a_off] in HKW. rewrite edenot_lit, u64_lit in HKW by lia. rewrite Z.add_0_l in HKW.
    change (Z.to_nat 8) with 8%nat in HKW.
    (* [comment removed for export] *)
    set (H2 := Hv E cs model).
    set (M0 := mrestrict H2 FULL).
    set (ms := mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)).
    assert (Hst0 : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true).
    { eapply store_ok_mono; [apply Mr_grows_Hv | exact HKW]. }
    assert (HM : forall a : word, STR0 <= bv_unsigned a <= STR0 + Z.of_nat (length s0) -> M0 a = wrap_mem inp mbase ph entry sp rdraw a).
    { intros a Ha. unfold M0, H2. rewrite mrestrict_Hv_high by (pose proof (APSK.utop_bounds E); rewrite (SINV_sp0 E FULL HS) in *; lia). eapply SINV_str0; [exact HS | exact Ha]. }
    destruct (pn_loop SEGS (x_pnscan A) wp0 wp1 wp2 wp3 wp4 ltac:(lia) Fp0 Fp1 Fp2 Fp3 Fp4 Ep0 Ep1 Ep2 Ep3 Ep4 Dp0 Dp1 Dp2 Dp3 Dp4
                M0 (seg_rom SEGS) p STR0 s0
                ltac:(unfold KHI in *; lia) ltac:(lia) ltac:(left; unfold KHI in *; lia)
                (valid_argv_str_nz (in_argv inp) 0 Hva ltac:(destruct Hva as [Hl _]; lia))
                (fun j Hj => rd_str0_j M0 j Hj HM) Hst0
                s0 0%nat R M0 eq_refl ltac:(lia) H10 H11' H12 (cellrel_refl M0 p)) as (R' & M' & Hms & Hpost & HM').
    unfold cfg_of. fold ms.
    assert (Hms' : msteps SEGS (restrict H2 ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS))).
    { unfold ms. rewrite restrict_mkst, Hpc. exact Hms. }
    apply (srz_msteps_restricted_T SEGS scfg H2 (H_off_segments_vis E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_vis E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H2 (ms_mem ms) (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) M' (seg_rom SEGS)))
      with (mkst R' (Z_to_bv 64 (x_pnscan A + 12)) (munrestrict H2 FULL M') (seg_rom SEGS)).
    set (FULL' := munrestrict H2 FULL M').
    assert (HF : forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> FULL' a = FULL a).
    { intros a Ha. unfold FULL', munrestrict. destruct (H2 a) eqn:H2a; [reflexivity|].
      destruct HM' as [HM1 _]. rewrite (HM1 a Ha). unfold M0, mrestrict. rewrite H2a. reflexivity. }
    (* [comment removed for export] *)
    set (v := nxt cs). set (E' := ext1 E v (getr R' 11%bv)).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
    pose proof (hid_agree A nx0 argH e_sp0_init argH_agree v E E' cs model Hag Fle Fallow) as Hhid.
    specialize (Hk E' R' FULL' model' (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
    unfold cfg_of, pc in Hk. cbn [a_ss with_ss mk_ss s_pc] in Hk. rewrite X3 in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame)].
    (* [comment removed for export] *)
    eapply cs_ok_frame; [exact SINV_frame | exact HC' | exact Hsame | | | reflexivity | |].
    - rewrite (allowA_agree A v E E' cs Hag Fallow). exact Hinv'.
    - cbn [s_regs]. destruct Hpost as (P11 & P13 & Pag).
      eapply (regs_ok_post2 E' _ R R' 11 11%bv _ 13 13%bv); [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | lia | lia | reflexivity | reflexivity | | |].
      + cbn [edenot]. unfold E'. rewrite ext1_at. reflexivity.
      + rewrite P13, edenot_lit. reflexivity.
      + intros r N1 N2. apply (Pag r). intros [H|H]; [exact (N1 H) | exact (N2 H)].
    - cbn [s_know]. unfold Mr. rewrite Hhid.
      apply (know_ok_havoc SEGS E' (mrestrict (hid A argH E cs model) FULL)).
      + apply kimg_cut_sound. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC') as HK'. unfold Mr in HK'. rewrite Hhid in HK'. exact HK'.
      + intros x Hx. unfold estart, elenZ in Hx. cbn [a_base a_off edenot] in Hx. rewrite !u64_lit in Hx by lia.
        unfold mrestrict. rewrite HF by lia. reflexivity.
      + intros x Hx. unfold mrestrict in *. destruct (hid A argH E cs model x) eqn:Hh; [exact Hx|].
        unfold FULL', munrestrict. unfold hid in Hh. apply orb_false_iff in Hh as [_ Hvx].
        unfold H2 at 1. unfold Hv. rewrite Hvx. cbn [negb].
        destruct HM' as [_ HM2]. apply HM2. unfold M0, mrestrict, H2, Hv. rewrite Hvx. cbn [negb]. exact Hx.
    - intros a Ha. rewrite Hhid in Ha. unfold hid in Ha. apply orb_prop in Ha as [Ha|Ha].
      + apply HF. right. pose proof (argH_high E a Ha). unfold CEIL, KHI in *. lia.
      + unfold FULL', munrestrict. unfold H2 at 1. unfold Hv. rewrite Ha. reflexivity.
  Qed.

End NodesD.

Lemma some_inj_acs : forall a b : acs, Some a = Some b -> a = b.
Proof. intros a b H. exact (f_equal (fun o => match o with Some x => x | None => a end) H). Qed.

Section LayoutSound.
  Variable SEGS : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  (* [comment removed for export] *)
  Variable rz : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  (* [comment removed for export] *)
  Lemma e_argv1w_ge2 : forall E, 2 <= bv_unsigned (ev E V_ARGC) -> edenot E (e_argv1w rz) = edenot E (e_str1 rz).
  Proof.
    intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit by lia.
    replace (1 <? bv_unsigned (ev E V_ARGC)) with true by (symmetry; apply Z.ltb_lt; lia).
    pose proof (u64_range (edenot E (e_str1 rz))). rewrite Z.mul_1_l. apply Z.mod_small. lia.
  Qed.

  Lemma e_argv1w_le1 : forall E, bv_unsigned (ev E V_ARGC) <= 1 -> edenot E (e_argv1w rz) = edenot E (ELit 0).
  Proof.
    intros E H. unfold e_argv1w. cbn [edenot]. apply bv_eq. rewrite u_mul64, u_sltu64, !u64_lit by lia.
    replace (1 <? bv_unsigned (ev E V_ARGC)) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  Qed.

  Lemma kw_argv1_respell : forall E M v v',
    kentry_ok SEGS E M (kw_argv1 v) -> edenot E v' = edenot E v -> kentry_ok SEGS E M (kw_argv1 v').
  Proof. intros E M v v' HK Hv. unfold kw_argv1 in *. cbn [kentry_ok] in *. rewrite Hv. exact HK. Qed.

  Theorem x_sound_layout : x_stmt SEGS scfg A nx0 LIMIT rz SINV argH FS0 XLayout.
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbn [node_x] in Hn. unfold node_layout in Hn.
    destruct (existsb (kentry_eqb (kw_argv1 (e_argv1w rz))) (kn cs)) eqn:Hex; [|discriminate]. cbn [negb] in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    (* [comment removed for export] *)
    apply existsb_exists in Hex as [K0 [Hin Heqb]]. apply kentry_eqb_eq in Heqb. subst K0.
    pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK0.
    assert (HK' : know_ok SEGS E (Mr A argH E cs model FULL)
                    (List.filter (fun K => negb (kentry_eqb (kw_argv1 (e_argv1w rz)) K)) (kn cs)))
      by (apply know_ok_filter; exact HK).
    assert (FIN : forall v, edenot E v = edenot E (e_argv1w rz) ->
                  cs' = set_kn cs (kw_argv1 v :: List.filter (fun K => negb (kentry_eqb (kw_argv1 (e_argv1w rz)) K)) (kn cs)) ->
                  srealizes SEGS scfg (cfg_of SEGS R (pc cs) FULL model) T).
    { intros v Hv ->. specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
      apply cs_ok_set_kn; [exact HC|]. constructor; [|exact HK'].
      eapply kw_argv1_respell; [exact HK0 | exact Hv]. }
    (* [comment removed for export] *)
    destruct args as [|[z| | | | | | |] [|e2 l2]]; try discriminate; destruct z as [|pz|pz]; try discriminate;
      try (destruct pz; try discriminate).
    - (* [comment removed for export] *)
      destruct (xhi (kn cs) (EVar V_ARGC)) as [hi|] eqn:Hhi; [|discriminate].
      destruct (Z.leb hi 1) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
      pose proof (xhi_sound SEGS E _ (kn cs) (EVar V_ARGC) hi HK Hhi) as B. cbn [edenot] in B.
      apply (FIN (ELit 0)); [|symmetry; exact Hn]. symmetry. apply e_argv1w_le1. lia.
    - (* [comment removed for export] *)
      destruct (xlo (kn cs) (EVar V_ARGC)) as [lo|] eqn:Hlo; [|discriminate].
      destruct (Z.leb 2 lo) eqn:Hle; [|discriminate]. apply Z.leb_le in Hle. apply some_inj_acs in Hn.
      pose proof (xlo_sound SEGS E _ (kn cs) (EVar V_ARGC) lo HK Hlo) as B. cbn [edenot] in B.
      apply (FIN (e_str1 rz)); [|symmetry; exact Hn]. symmetry. apply e_argv1w_ge2. lia.
  Qed.
End LayoutSound.
End AsanNodesStartXK.
Module AsanNodesStartXInitK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanNodesAuxK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.AsanStartLoops OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanNodesStartXK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2K. Import AX2SK. Import APK. Import APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section GenericInit.
  (* [comment removed for export] *)
  Variable segs : list Segment.
  Variable scfg : SpuriousCfg.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Hypothesis SEGS_wx : wx_segs_nowrap segs.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.

  (* [comment removed for export] *)
  Variables we1 we2 we3 wp0 wp1 wp2 wp3 wp4 : bv 32.
  Hypothesis Xenv : 0 <= x_envscan A /\ x_envscan A + 12 < 2 ^ 64 /\ x_envscan_k A = x_envscan A + 12.
  Hypothesis Fe1 : fetch_word segs (Z_to_bv 64 (x_envscan A)) = Some we1.
  Hypothesis Fe2 : fetch_word segs (Z_to_bv 64 (x_envscan A + 4)) = Some we2.
  Hypothesis Fe3 : fetch_word segs (Z_to_bv 64 (x_envscan A + 8)) = Some we3.
  Hypothesis Ee : is_ecall we1 = false /\ is_ecall we2 = false /\ is_ecall we3 = false.
  Hypothesis De1 : decode_any we1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis De2 : decode_any we2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis De3 : decode_any we3 = Some (Branch BC_NE 10 0 8184, 4%Z).
  Hypothesis Xpn : 8 <= x_pnscan A /\ x_pnscan A + 12 < 2 ^ 64 /\ x_pnscan_k A = x_pnscan A + 12.
  Hypothesis Fp0 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 8)) = Some wp0.
  Hypothesis Fp1 : fetch_word segs (Z_to_bv 64 (x_pnscan A - 4)) = Some wp1.
  Hypothesis Fp2 : fetch_word segs (Z_to_bv 64 (x_pnscan A)) = Some wp2.
  Hypothesis Fp3 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 4)) = Some wp3.
  Hypothesis Fp4 : fetch_word segs (Z_to_bv 64 (x_pnscan A + 8)) = Some wp4.
  Hypothesis Ep : is_ecall wp0 = false /\ is_ecall wp1 = false /\ is_ecall wp2 = false /\ is_ecall wp3 = false /\ is_ecall wp4 = false.
  Hypothesis Dp0 : decode_any wp0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis Dp1 : decode_any wp1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Dp2 : decode_any wp2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis Dp3 : decode_any wp3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis Dp4 : decode_any wp4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  Variable apc : N.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Notation INP :=
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation ENTRY := (Z_to_bv 64 (Z.of_N apc)).
  #[local] Notation E00 :=
    (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  (* [comment removed for export] *)
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.

  (* [comment removed for export] *)
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M ->
    SINV0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc E M.
  Hypothesis SINV_frame : forall E M M',
    (forall a, argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf E a = true -> M' a = M a) ->
    SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.

  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let s0 := nth 0 argv [].
  (* [comment removed for export] *)
  Let rseq := kb_rseq (in_kernel INP).
  Let top := ed_top rdraw.

  Lemma sp_lo : sp_window_lo <= bv_unsigned sp.
  Proof. destruct Hsp as [H _]. exact H. Qed.
  Lemma sp_hi : bv_unsigned sp <= sp_window_hi.
  Proof. destruct Hsp as (_ & H & _). exact H. Qed.

  (* [comment removed for export] *)
  Lemma inp_fields :
    in_argv INP = argv /\ in_envp INP = envp /\ in_execfn INP = execfn.
  Proof. repeat split. Qed.

  (* [comment removed for export] *)
  Lemma SINV0_vals : forall E M, SINV E M ->
    uE E e_envp = usp + 8 * argc + 16
    /\ ev E V_ENVC = Z_to_bv 64 envc
    /\ uE E (e_str0 (rseq_z rseq)) = usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn).
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    pose proof (u_e_envp ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as U1.
    pose proof (u_e_str0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as U3.
    pose proof (uE0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as (_ & _ & _ & U2 & _).
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E00 n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE in *. unfold rseq in *.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (kb_rseq (in_kernel INP)) eqn:Hrs; rewrite ?Hrs in U1, U2, U3; cbn [rseq_z];
      rewrite (edenot_ev_agree NX0 E E00 e_envp eq_refl Hev7);
      lazymatch goal with |- context [edenot E (e_str0 ?k)] =>
        rewrite (edenot_ev_agree NX0 E E00 (e_str0 k) eq_refl Hev7) end;
      (split; [exact U1|]); (split; [|exact U3]);
      change (ev E V_ENVC) with (edenot E (EVar V_ENVC));
      rewrite (edenot_ev_agree NX0 E E00 (EVar V_ENVC) eq_refl Hev7);
      apply bv_eq; rewrite U2; unfold envc; destruct Hve as [Hvec _];
      rewrite u64_lit by lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma SINV0_sp0 : forall E M, SINV E M -> uE E e_sp0 = usp.
  Proof.
    intros E M HS. apply SINV_SINV0 in HS. destruct HS as [Hev _].
    assert (Hev7 : forall n, (n < NX0)%nat -> ev E n = ev E00 n) by (intros n Hn; apply Hev; exact Hn).
    unfold uE. rewrite (edenot_ev_agree NX0 E E00 e_sp0 eq_refl Hev7).
    exact (u_e_sp0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau).
  Qed.

  Lemma SINV0_envp : forall E M (a : word), SINV E M ->
    usp + 8 * argc + 16 <= bv_unsigned a < usp + 8 * argc + 16 + 8 * envc + 8 ->
    M a = wrap_mem INP mbase ph ENTRY sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0.
    pose proof (proj1 Hva) as AV. fold argc in AV.
    apply andb_true_intro. split; [apply Z.leb_le; rewrite US; lia|].
    (* [comment removed for export] *)
    apply orb_true_intro. left.
    apply andb_true_intro. unfold usp, argc, envc in Ha. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma s0_le_strings :
    Z.of_nat (length s0) + 1 <= Z.of_nat (launch_string_bytes argv envp execfn).
  Proof.
    assert (Hnz : (0 < length argv)%nat) by (destruct Hva as [[H _] _]; lia).
    unfold launch_string_bytes, s0.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings envp))).
    pose proof (Nat2Z.is_nonneg (length execfn)).
    destruct argv as [|a t] eqn:Ea; [cbn in Hnz; lia|].
    cbn [flatten_strings flat_map nth]. rewrite !length_app. cbn [length]. lia.
  Qed.

  Lemma bsb_len_sum :
    Z.of_nat (length (entry_stack_image INP mbase ph ENTRY sp rdraw))
    = Z.of_nat (cat_string_off rseq sp top argv envp execfn)
      + Z.of_nat (launch_string_bytes argv envp execfn) + 8.
  Proof.
    rewrite entry_stack_image_block, length_build_stack_bytes.
    unfold cat_string_off, rseq, top.
    change (la_rseq (launch_auxv INP sp mbase)) with (kb_rseq (in_kernel INP)).
    destruct inp_fields as (Q1 & Q2 & Q3). rewrite ?Q1, ?Q2, ?Q3. lia.
  Qed.

  Lemma str0_lt_top :
    usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + Z.of_nat (length s0)
    < bv_unsigned top.
  Proof.
    pose proof bsb_len_sum as S. pose proof s0_le_strings as F.
    pose proof (length_bsb_eq ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hlau) as L.
    unfold stack_image_size in L. unfold usp, top in *. lia.
  Qed.

  Lemma SINV0_str0 : forall E M (a : word), SINV E M ->
    usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) <= bv_unsigned a
      <= usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn) + Z.of_nat (length s0) ->
    M a = wrap_mem INP mbase ph ENTRY sp rdraw a.
  Proof.
    intros E M a HS Ha. pose proof (SINV0_sp0 E M HS) as US. apply SINV_SINV0 in HS. destruct HS as [_ HM]. apply HM. unfold argH0.
    pose proof (Nat2Z.is_nonneg (cat_string_off rseq sp top argv envp execfn)) as CN.
    pose proof str0_lt_top as ST.
    apply andb_true_intro. split; [apply Z.leb_le; rewrite US; unfold usp in *; lia|].
    apply orb_true_intro. right.
    apply andb_true_intro. unfold usp, rseq, top in *. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  (* [comment removed for export] *)
  Theorem init_x_sound_envscan :
    x_stmt segs scfg A NX0 LIMIT (rseq_z rseq) SINV
      (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0 XEnvScan.
  Proof.
    eapply (x_sound_envscan segs scfg A NX0 LIMIT SINV
              (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0
              SEGS_wx SEGS_in_hull HULL_ok SINV_frame
              we1 we2 we3 Xenv Fe1 Fe2 Fe3 Ee De1 De2 De3
              ph INP mbase ENTRY sp brk0 rdraw);
      try exact Hva; try exact Hve; try exact Hlaunch; try exact Hlau;
      try exact sp_lo; try exact sp_hi;
      try exact SINV0_vals; try exact SINV0_sp0; try exact SINV0_envp; try exact SINV0_str0.
  Qed.

  Theorem init_x_sound_pnscan :
    x_stmt segs scfg A NX0 LIMIT (rseq_z rseq) SINV
      (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0 XPnScan.
  Proof.
    eapply (x_sound_pnscan segs scfg A NX0 LIMIT SINV
              (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0
              SEGS_wx SEGS_in_hull HULL_ok
              (argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva)
              e_sp0_init
              (argH0_agree sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf)
              SINV_frame SINV_agree
              wp0 wp1 wp2 wp3 wp4 Xpn Fp0 Fp1 Fp2 Fp3 Fp4 Ep Dp0 Dp1 Dp2 Dp3 Dp4
              ph INP mbase ENTRY sp brk0 rdraw);
      try exact Hva; try exact Hve; try exact Hlaunch; try exact Hlau;
      try exact sp_lo; try exact sp_hi;
      try exact SINV0_vals; try exact SINV0_sp0; try exact SINV0_envp; try exact SINV0_str0.
  Qed.

  Theorem init_x_sound_layout :
    x_stmt segs scfg A NX0 LIMIT (rseq_z rseq) SINV
      (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) FS0 XLayout.
  Proof. apply x_sound_layout. Qed.
End GenericInit.
End AsanNodesStartXInitK.
Module HandoffBridgeK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* [comment removed for export] *)
Definition VZ (E : env) (n : nat) : Z := bv_unsigned (ev E n).
(* [comment removed for export] *)
Definition LZ (E : env) (e : expr) : Z := lden E (lin_of e).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Generic.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.   (* [comment removed for export] *)

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation MR := (Mr A argH).
#[local] Notation HID := (hid A argH).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_kn : forall E cs R FULL model K,
  CSOK E cs R FULL model -> In K (kn cs) -> kentry_ok SEGS E (MR E cs model FULL) K.
Proof. intros E cs R FULL model K HC Hin. exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin). Qed.

(* [comment removed for export] *)
Lemma hb_knb_In : forall K k, existsb (kentry_eqb K) k = true -> In K k.
Proof.
  intros K k H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin.
Qed.

Lemma hb_knb : forall E cs R FULL model K,
  CSOK E cs R FULL model -> existsb (kentry_eqb K) (kn cs) = true -> kentry_ok SEGS E (MR E cs model FULL) K.
Proof. intros E cs R FULL model K HC H. exact (hb_kn E cs R FULL model K HC (hb_knb_In K _ H)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_mr_some : forall E cs model FULL (a : word) b,
  MR E cs model FULL a = Some b -> FULL a = Some b.
Proof. intros E cs model FULL a b H. unfold Mr, mrestrict in H. destruct (HID E cs model a); [discriminate| exact H]. Qed.

Lemma hb_mr_visible : forall E cs model FULL (a : word) b,
  MR E cs model FULL a = Some b -> HID E cs model a = false.
Proof. intros E cs model FULL a b H. unfold Mr, mrestrict in H. destruct (HID E cs model a); [discriminate| reflexivity]. Qed.

Lemma hb_mr_rdn : forall E cs model FULL (a : word) n bs,
  rdn SEGS (MR E cs model FULL) a n = Some bs ->
  rdn SEGS FULL a n = Some bs /\ range_avoids (HID E cs model) a n.
Proof.
  intros E cs model FULL a n bs H. unfold Mr in H. rewrite <- ov_rdn in H |- *.
  exact (ov_read_bytes_restrict SEGS _ (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) n FULL a bs H).
Qed.

Lemma hb_mr_store_ok : forall E cs model FULL (a : word) n,
  store_ok SEGS (MR E cs model FULL) a n = true ->
  store_ok SEGS FULL a n = true /\ range_avoids (HID E cs model) a n.
Proof.
  intros E cs model FULL a n H. unfold Mr in H.
  exact (store_ok_restrict SEGS _ (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) n FULL a H).
Qed.

(* [comment removed for export] *)
Lemma hb_mr_hull : forall E cs model FULL (a : word),
  in_hull A (bv_unsigned a) = true -> MR E cs model FULL a = FULL a.
Proof. intros E cs model FULL a H. unfold Mr, mrestrict. rewrite (hid_hull A HULL_ok argH argH_high E cs model a H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_lin : forall E cs R FULL model e,
  CSOK E cs R FULL model -> lin_nowrapR (kn cs) e = true -> bv_unsigned (edenot E e) = LZ E e.
Proof. intros E cs R FULL model e HC H. exact (lin_nowrapR_sound SEGS E _ (kn cs) e (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.

Lemma hb_xlo : forall E cs R FULL model e lo,
  CSOK E cs R FULL model -> xlo (kn cs) e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof. intros E cs R FULL model e lo HC H. exact (xlo_sound SEGS E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.

Lemma hb_xhi : forall E cs R FULL model e hi,
  CSOK E cs R FULL model -> xhi (kn cs) e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof. intros E cs R FULL model e hi HC H. exact (xhi_sound SEGS E _ (kn cs) e hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.

(* [comment removed for export] *)
Lemma hb_bounds_e : forall E cs R FULL model e lo hi,
  CSOK E cs R FULL model -> xlo (kn cs) e = Some lo -> xhi (kn cs) e = Some hi ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof. intros E cs R FULL model e lo hi HC H1 H2. split; [eapply hb_xlo; eassumption | eapply hb_xhi; eassumption]. Qed.

Lemma hb_estart : forall E b off, estart E (SA b off) = bv_unsigned (edenot E b) + off.
Proof. reflexivity. Qed.

Lemma hb_adenot : forall E a n, flat E a n -> adenot E a = Z_to_bv 64 (estart E a).
Proof.
  intros E a n Hf. apply bv_eq. rewrite (flat_u E a n Hf). destruct Hf as (H1 & H2 & _).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_word : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> In (KWord a w v) (kn cs) ->
  (w <= 8)%nat /\ flat E a (Z.of_nat w)
  /\ rdn SEGS FULL (adenot E a) w = Some (word_to_le_bytes w (edenot E v))
  /\ range_avoids (HID E cs model) (adenot E a) w.
Proof.
  intros E cs R FULL model a w v HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as (Hw & Hf & Hr).
  destruct (hb_mr_rdn E cs model FULL _ _ _ Hr) as [H1 H2]. auto.
Qed.

(* [comment removed for export] *)
Lemma hb_rdn_bytes : forall FULL n (a0 : word) bs,
  rdn SEGS FULL a0 n = Some bs ->
  (forall j, (j < n)%nat -> in_hull A (bv_unsigned a0 + Z.of_nat j) = false) ->
  bv_unsigned a0 + Z.of_nat n <= 2 ^ 64 ->
  forall j, (j < n)%nat -> FULL (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros FULL n. induction n as [|n IH]; intros a0 bs Hrd Hh Hnw j Hj; [lia|].
  cbn [rdn] in Hrd.
  destruct (FULL a0) as [b|] eqn:Hb.
  - destruct (rdn SEGS FULL (a0 + 1)%bv n) as [rest|] eqn:Hr2; [|discriminate]. injection Hrd as <-.
    destruct j as [|j].
    + cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hb.
    + cbn [nth]. pose proof (u64_range a0).
      assert (Hu1 : bv_unsigned (a0 + 1)%bv = bv_unsigned a0 + 1) by (apply u_add1; lia).
      replace (bv_unsigned a0 + Z.of_nat (Datatypes.S j)) with (bv_unsigned (a0 + 1)%bv + Z.of_nat j) by lia.
      apply (IH (a0 + 1)%bv rest Hr2); [| lia | lia].
      intros j' Hj'. rewrite Hu1. replace (bv_unsigned a0 + 1 + Z.of_nat j') with (bv_unsigned a0 + Z.of_nat (Datatypes.S j')) by lia. apply Hh. lia.
  - (* [comment removed for export] *)
    exfalso. pose proof (Hh 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
    unfold seg_rom, memory_read in Hrd. cbn [Z.of_N] in Hrd. rewrite (SEGS_in_hull a0 H0) in Hrd. discriminate.
Qed.

(* [comment removed for export] *)
Lemma hb_word_bytes : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> In (KWord a w v) (kn cs) ->
  (forall j, (j < w)%nat -> in_hull A (estart E a + Z.of_nat j) = false) ->
  forall j, (j < w)%nat ->
    FULL (Z_to_bv 64 (estart E a + Z.of_nat j)) = Some (nth j (word_to_le_bytes w (edenot E v)) (Z_to_bv 8 0)).
Proof.
  intros E cs R FULL model a w v HC Hin Hoff j Hj.
  destruct (hb_word E cs R FULL model a w v HC Hin) as (Hw & Hf & Hr & _).
  pose proof (flat_u E a _ Hf) as Hu. rewrite <- Hu. rewrite <- Hu in Hoff.
  apply (hb_rdn_bytes FULL w (adenot E a) _ Hr Hoff); [|exact Hj].
  destruct Hf as (?&?&?&?). rewrite Hu. lia.
Qed.

(* [comment removed for export] *)
Lemma hb_zero_k : forall E cs R FULL model a n,
  CSOK E cs R FULL model -> In (KZero a n) (kn cs) ->
  flat E a (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
  split; [exact Hf|]. intros i Hi. exact (hb_mr_some E cs model FULL _ _ (Hz i Hi)).
Qed.

(* [comment removed for export] *)
Lemma hb_fill : forall E cs R FULL model a n c,
  CSOK E cs R FULL model -> In (KFill a n c) (kn cs) ->
  flat E a (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 c).
Proof.
  intros E cs R FULL model a n c HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
  split; [exact Hf|]. intros i Hi. exact (hb_mr_some E cs model FULL _ _ (Hz i Hi)).
Qed.

(* [comment removed for export] *)
Lemma hb_unk : forall E cs R FULL model a n,
  CSOK E cs R FULL model -> In (KUnk a n) (kn cs) ->
  flat E a (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E a + i)) <> None.
Proof.
  intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
  split; [exact Hf|]. intros i Hi Hn. apply (Hz i Hi). unfold Mr, mrestrict. rewrite Hn. destruct (HID E cs model _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hb_img : forall E cs R FULL model lo hi,
  CSOK E cs R FULL model -> In (KImg lo hi) (kn cs) ->
  forall i, lo <= i < hi -> in_hull A i = true -> FULL (Z_to_bv 64 i) = None.
Proof.
  intros E cs R FULL model lo hi HC Hin i Hi Hh. destruct (hb_kn E cs R FULL model _ HC Hin) as (H0 & H1 & Hn).
  rewrite <- (hb_mr_hull E cs model FULL (Z_to_bv 64 i)); [exact (Hn i Hi)|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [exact Hh| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma hb_wr : forall E cs R FULL model a n,
  CSOK E cs R FULL model -> In (KWr a n) (kn cs) ->
  flat E a (elenZ E n)
  /\ forall d m, 0 <= d -> d + Z.of_nat m <= elenZ E n ->
       store_ok SEGS FULL (Z_to_bv 64 (estart E a + d)) m = true
       /\ range_avoids (HID E cs model) (Z_to_bv 64 (estart E a + d)) m.
Proof.
  intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hs].
  split; [exact Hf|]. intros d m Hd Hm. exact (hb_mr_store_ok E cs model FULL _ _ (Hs d m Hd Hm)).
Qed.

(* [comment removed for export] *)
Lemma hb_range : forall E cs R FULL model e lo hi,
  CSOK E cs R FULL model -> In (KRange e lo hi) (kn cs) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof. intros E cs R FULL model e lo hi HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [H1 H2]. lia. Qed.

Lemma hb_disj : forall E cs R FULL model a1 n1 a2 n2,
  CSOK E cs R FULL model -> In (KDisj a1 n1 a2 n2) (kn cs) ->
  estart E a1 + elenZ E n1 <= estart E a2 \/ estart E a2 + elenZ E n2 <= estart E a1.
Proof. intros E cs R FULL model a1 n1 a2 n2 HC Hin. exact (hb_kn E cs R FULL model _ HC Hin). Qed.

Lemma hb_align : forall E cs R FULL model e m,
  CSOK E cs R FULL model -> In (KAlign e m) (kn cs) -> 0 < m /\ bv_unsigned (edenot E e) mod m = 0.
Proof. intros E cs R FULL model e m HC Hin. exact (hb_kn E cs R FULL model _ HC Hin). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_reg : forall E cs R FULL model (r : bv 5),
  CSOK E cs R FULL model -> getr R r = edenot E (sr_get (s_regs (a_ss cs)) r).
Proof. intros E cs R FULL model r HC. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r). Qed.

Lemma hb_regZ : forall E cs R FULL model (r : bv 5),
  CSOK E cs R FULL model -> lin_nowrapR (kn cs) (sr_get (s_regs (a_ss cs)) r) = true ->
  bv_unsigned (getr R r) = LZ E (sr_get (s_regs (a_ss cs)) r).
Proof. intros E cs R FULL model r HC H. rewrite (hb_reg E cs R FULL model r HC). exact (hb_lin E cs R FULL model _ HC H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_maps : forall E cs R FULL model,
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  vm_maps (m_vmmaps model) = map (amap_den E) (a_maps cs).
Proof.
  intros E cs R FULL model HC Hnf.
  exact (proj1 (maps_match_exact 0%nat (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E (a_maps cs) _ Hnf)
               (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)).
Qed.

(* [comment removed for export] *)
Definition amapZ (E : env) (m : amap) : Z * Z := (LZ E (am_base m), LZ E (am_base m) + LZ E (am_len m)).
Definition amaps_lin (k : list kentry) (ms : list amap) : bool :=
  forallb (fun m => lin_nowrapR k (am_base m) && lin_nowrapR k (am_len m)) ms.

Lemma hb_maps_Z : forall E cs R FULL model,
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true -> amaps_lin (kn cs) (a_maps cs) = true ->
  map (fun e => (B e, B e + S e)) (vm_maps (m_vmmaps model)) = map (amapZ E) (a_maps cs).
Proof.
  intros E cs R FULL model HC Hnf Hl. rewrite (hb_maps E cs R FULL model HC Hnf). rewrite map_map. apply map_ext_in.
  intros m Hm. unfold amaps_lin in Hl. pose proof (proj1 (forallb_forall _ _) Hl m Hm) as Hb. apply andb_prop in Hb as [H1 H2].
  unfold amapZ, amap_den, B, S. cbn [fst snd].
  rewrite (hb_lin E cs R FULL model _ HC H1), (hb_lin E cs R FULL model _ HC H2). reflexivity.
Qed.

(* [comment removed for export] *)

Lemma hb_limit : forall E cs R FULL model, CSOK E cs R FULL model -> vm_limit (m_vmmaps model) = LIMIT.
Proof. intros E cs R FULL model HC. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_brk : forall E cs R FULL model, CSOK E cs R FULL model -> vm_brk (m_vmmaps model) = edenot E (a_brk cs).
Proof. intros E cs R FULL model HC. exact (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_brkZ : forall E cs R FULL model,
  CSOK E cs R FULL model -> lin_nowrapR (kn cs) (a_brk cs) = true -> bv_unsigned (vm_brk (m_vmmaps model)) = LZ E (a_brk cs).
Proof. intros E cs R FULL model HC H. rewrite (hb_brk E cs R FULL model HC). exact (hb_lin E cs R FULL model _ HC H). Qed.

Lemma hb_sbrk : forall E cs R FULL model,
  CSOK E cs R FULL model -> bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model)).
Proof. intros E cs R FULL model HC. exact (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma hb_isp : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  bv_unsigned (vm_init_sp (m_vmmaps model)) = uE E e_sp0 /\ sp_window_lo <= uE E e_sp0 <= sp_window_hi
  /\ uE E e_sppg = pagedown (uE E e_sp0).
Proof. intros E cs R FULL model HC. exact (co_isp _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_seps : forall E cs R FULL model, CSOK E cs R FULL model -> seps (vm_maps (m_vmmaps model)).
Proof. intros E cs R FULL model HC. exact (co_seps _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_wf : forall E cs R FULL model, CSOK E cs R FULL model -> model_ivs_wf model.
Proof. intros E cs R FULL model HC. exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_bounds : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E)
         (vm_maps (m_vmmaps model)).   (* [comment removed for export] *)
Proof. intros E cs R FULL model HC. exact (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_lazyb : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E) (m_vm_lazy model).
Proof. intros E cs R FULL model HC. exact (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_nasub : forall E cs R FULL model z,
  CSOK E cs R FULL model -> in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true.
Proof. intros E cs R FULL model z HC. exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC z). Qed.

Lemma hb_totsz : forall E cs R FULL model,
  CSOK E cs R FULL model -> sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs.
Proof. intros E cs R FULL model HC. exact (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma hb_none : forall E cs R FULL model m,
  CSOK E cs R FULL model -> In m (a_maps cs) -> am_kind m = KNONE \/ am_kind m = KNONELAZY ->
  In (amap_den E m) (vm_noaccess (m_vmmaps model)).
Proof. intros E cs R FULL model m HC Hm Hk. exact (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hk). Qed.

(* [comment removed for export] *)
Lemma hb_lazykind : forall E cs R FULL model m (a : word),
  CSOK E cs R FULL model -> In m (a_maps cs) -> am_kind m = KRWLAZY ->
  bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false /\ page_in_ranges (page_base a) (m_vm_lazy model) = true.
Proof. intros E cs R FULL model m a HC Hm Hk Ha. exact (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hk a Ha). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_noacc : forall E cs R FULL model, CSOK E cs R FULL model -> vm_noaccess (m_vmmaps model) = hreplay E (a_hna cs).
Proof. intros E cs R FULL model HC. exact (co_hna _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_lazy : forall E cs R FULL model, CSOK E cs R FULL model -> m_vm_lazy model = hreplay E (a_hlz cs).
Proof. intros E cs R FULL model HC. exact (co_hlz _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_tid : forall E cs R FULL model, CSOK E cs R FULL model -> a_tidset cs = true ->
  exists t, m_tid model = Some t /\ 0 < bv_unsigned t < PID_MAX.
Proof. intros E cs R FULL model HC Ht. exact (co_tidv _ _ _ _ _ _ _ _ _ _ _ HC Ht). Qed.

(* [comment removed for export] *)
Lemma hb_tid_range : forall E cs R FULL model, CSOK E cs R FULL model -> a_tidset cs = true ->
  forall t, m_tid model = Some t -> 0 < bv_unsigned t < 4194304.
Proof.
  intros E cs R FULL model HC Ht t Hm. destruct (hb_tid E cs R FULL model HC Ht) as (t' & Hm' & Hr).
  rewrite Hm in Hm'. injection Hm' as ->. unfold PID_MAX in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma hreplay_nil : forall E, hreplay E [] = []. Proof. reflexivity. Qed.
Lemma hreplay_cons : forall E b n h, hreplay E (HCons b n :: h) = (edenot E b, edenot E n) :: hreplay E h. Proof. reflexivity. Qed.
Lemma hreplay_sub : forall E b n h,
  hreplay E (HSub b n :: h) = maps_subtract (hreplay E h) (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_eager : forall E cs R FULL model, CSOK E cs R FULL model -> eager_used model <= a_eager cs.
Proof. intros E cs R FULL model HC. exact (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_abytes : forall E cs R FULL model, CSOK E cs R FULL model -> A_bytes (allowA A E cs) <= a_abytes cs.
Proof. intros E cs R FULL model HC. exact (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_minv : forall E cs R FULL model, CSOK E cs R FULL model -> MInv (allowA A E cs) model.
Proof. intros E cs R FULL model HC. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_allowA_wf : forall E cs, A_wf (allowA A E cs).
Proof. intros E cs. exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs). Qed.

(* [comment removed for export] *)
Definition allow1Z (E : env) (p : expr * expr) : list (Z * Z) :=
  let b := LZ E (fst p) in let n := LZ E (snd p) in
  [(pagedown b, pageup (b + n)); (pagedown (shadow_off A + b / 8), pageup (shadow_off A + (b + n) / 8))].
Definition vis_lin (k : list kentry) (ps : list (expr * expr)) : bool :=
  forallb (fun p => lin_nowrapR k (fst p) && lin_nowrapR k (snd p)) ps.

Lemma flat_map_ext_In {X Y} : forall (f g : X -> list Y) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. intros f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

Lemma hb_allowA_Z : forall E cs R FULL model,
  CSOK E cs R FULL model -> vis_lin (kn cs) (a_vis cs ++ a_ghost cs) = true ->
  allowA A E cs = flat_map (allow1Z E) (a_vis cs ++ a_ghost cs).
Proof.
  intros E cs R FULL model HC Hl. unfold allowA. apply flat_map_ext_In.
  intros p Hp. pose proof (proj1 (forallb_forall _ _) Hl p Hp) as Hb. apply andb_prop in Hb as [H1 H2].
  unfold allow1, allow1Z, sh_lo, sh_hi, APSK.uE. rewrite (hb_lin E cs R FULL model _ HC H1), (hb_lin E cs R FULL model _ HC H2). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_halt : forall E cs R FULL model, CSOK E cs R FULL model -> m_halted model = None.
Proof. intros E cs R FULL model HC. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_fds_std : forall E cs R FULL model, CSOK E cs R FULL model -> a_fd cs = FdStd -> m_fds model = fds_std.
Proof. intros E cs R FULL model HC Hfd. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as H. rewrite Hfd in H. exact H. Qed.

Lemma hb_fs : forall E cs R FULL model, CSOK E cs R FULL model -> m_fs model = FS0.
Proof. intros E cs R FULL model HC. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma hb_tid_none : forall E cs R FULL model, CSOK E cs R FULL model -> a_tidset cs = false -> m_tid model = None.
Proof. intros E cs R FULL model HC. exact (co_tid _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_zero : forall E cs R FULL model (a : word),
  CSOK E cs R FULL model ->
  HID E cs model a = true ->
  in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
  in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
  page_in_ranges (page_base a) (m_vm_lazy model) = true ->
  in_ghost E cs (bv_unsigned a) = false ->
  FULL a = Some (Z_to_bv 8 0).
Proof. intros E cs R FULL model a HC. exact (co_zero _ _ _ _ _ _ _ _ _ _ _ HC a). Qed.

(* [comment removed for export] *)
Lemma hb_hid_unfold : forall E cs model (a : word),
  HID E cs model a = (argH E a || negb (vis A E cs model a))%bool.
Proof. reflexivity. Qed.

Lemma hb_sinv : forall E cs R FULL model, CSOK E cs R FULL model -> SINV E FULL.
Proof. intros E cs R FULL model HC. exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kfind_word (k : list kentry) (b : expr) (off : Z) (w : nat) : option expr :=
  match List.find (fun K => match K with
                            | KWord a w' _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off && Nat.eqb w' w)%bool
                            | _ => false end) k with
  | Some (KWord _ _ v) => Some v
  | _ => None
  end.

Lemma kfind_word_In : forall k b off w v, kfind_word k b off w = Some v -> In (KWord (SA b off) w v) k.
Proof.
  intros k b off w v H. unfold kfind_word in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [a w' v'| | | | | | | | |]; try discriminate.
  injection H as <-. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Nat.eqb_eq in H3. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.

Lemma hb_word_at : forall E cs R FULL model b off w v,
  CSOK E cs R FULL model -> kfind_word (kn cs) b off w = Some v ->
  (w <= 8)%nat /\ flat E (SA b off) (Z.of_nat w)
  /\ rdn SEGS FULL (adenot E (SA b off)) w = Some (word_to_le_bytes w (edenot E v))
  /\ range_avoids (HID E cs model) (adenot E (SA b off)) w.
Proof. intros E cs R FULL model b off w v HC H. exact (hb_word E cs R FULL model _ w v HC (kfind_word_In _ _ _ _ _ H)). Qed.

(* [comment removed for export] *)
Definition kfind_zero (k : list kentry) (b : expr) (off : Z) : option expr :=
  match List.find (fun K => match K with
                            | KZero a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                            | _ => false end) k with
  | Some (KZero _ n) => Some n
  | _ => None
  end.
Lemma kfind_zero_In : forall k b off n, kfind_zero k b off = Some n -> In (KZero (SA b off) n) k.
Proof.
  intros k b off n H. unfold kfind_zero in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ |a n'| | | | | | | |]; try discriminate.
  injection H as <-. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_zero_at : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> kfind_zero (kn cs) b off = Some n ->
  flat E (SA b off) (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0).
Proof. intros E cs R FULL model b off n HC H. exact (hb_zero_k E cs R FULL model _ n HC (kfind_zero_In _ _ _ _ H)). Qed.

Definition kfind_fill (k : list kentry) (b : expr) (off : Z) : option (expr * Z) :=
  match List.find (fun K => match K with
                            | KFill a _ _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                            | _ => false end) k with
  | Some (KFill _ n c) => Some (n, c)
  | _ => None
  end.
Lemma kfind_fill_In : forall k b off n c, kfind_fill k b off = Some (n, c) -> In (KFill (SA b off) n c) k.
Proof.
  intros k b off n c H. unfold kfind_fill in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | | | | | | | |a n' c'| ]; try discriminate.
  injection H as <- <-. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_fill_at : forall E cs R FULL model b off n c,
  CSOK E cs R FULL model -> kfind_fill (kn cs) b off = Some (n, c) ->
  flat E (SA b off) (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 c).
Proof. intros E cs R FULL model b off n c HC H. exact (hb_fill E cs R FULL model _ n c HC (kfind_fill_In _ _ _ _ _ H)). Qed.

Definition kfind_wr (k : list kentry) (b : expr) (off : Z) : option expr :=
  match List.find (fun K => match K with
                            | KWr a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                            | _ => false end) k with
  | Some (KWr _ n) => Some n
  | _ => None
  end.
Lemma kfind_wr_In : forall k b off n, kfind_wr k b off = Some n -> In (KWr (SA b off) n) k.
Proof.
  intros k b off n H. unfold kfind_wr in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | | | | | |a n'| | | ]; try discriminate.
  injection H as <-. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_wr_at : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> kfind_wr (kn cs) b off = Some n ->
  flat E (SA b off) (elenZ E n)
  /\ forall d m, 0 <= d -> d + Z.of_nat m <= elenZ E n ->
       store_ok SEGS FULL (Z_to_bv 64 (estart E (SA b off) + d)) m = true
       /\ range_avoids (HID E cs model) (Z_to_bv 64 (estart E (SA b off) + d)) m.
Proof. intros E cs R FULL model b off n HC H. exact (hb_wr E cs R FULL model _ n HC (kfind_wr_In _ _ _ _ H)). Qed.

(* [comment removed for export] *)
Definition kfind_img (k : list kentry) (z : Z) : option (Z * Z) :=
  match List.find (fun K => match K with KImg lo hi => (Z.leb lo z && Z.ltb z hi)%bool | _ => false end) k with
  | Some (KImg lo hi) => Some (lo, hi)
  | _ => None
  end.
Lemma kfind_img_In : forall k z lo hi, kfind_img k z = Some (lo, hi) -> In (KImg lo hi) k /\ lo <= z < hi.
Proof.
  intros k z lo hi H. unfold kfind_img in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | | |lo' hi'| | | | | | ]; try discriminate.
  injection H as <- <-. apply andb_prop in HK as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
Qed.
Lemma hb_img_at : forall E cs R FULL model z lo hi,
  CSOK E cs R FULL model -> kfind_img (kn cs) z = Some (lo, hi) ->
  forall i, lo <= i < hi -> in_hull A i = true -> FULL (Z_to_bv 64 i) = None.
Proof. intros E cs R FULL model z lo hi HC H. destruct (kfind_img_In _ _ _ _ H) as [Hin _]. exact (hb_img E cs R FULL model lo hi HC Hin). Qed.

(* [comment removed for export] *)
Definition kfind_at (k : list kentry) (b : expr) (off : Z) : list kentry :=
  List.filter (fun K => match K with
                        | KWord a _ _ | KZero a _ | KBlob a _ _ | KWr a _ | KFill a _ _ | KUnk a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                        | _ => false end) k.
Lemma kfind_at_In : forall k b off K, In K (kfind_at k b off) -> In K k.
Proof. intros k b off K H. unfold kfind_at in H. apply filter_In in H as [H _]. exact H. Qed.

(* [comment removed for export] *)
Definition kfind_ranges (k : list kentry) (e : expr) : list (Z * Z) :=
  flat_map (fun K => match K with KRange e' lo hi => if expr_eqb e' e then [(lo, hi)] else [] | _ => [] end) k.
Lemma hb_ranges_of : forall E cs R FULL model e,
  CSOK E cs R FULL model -> Forall (fun r => fst r <= bv_unsigned (edenot E e) <= snd r) (kfind_ranges (kn cs) e).
Proof.
  intros E cs R FULL model e HC. unfold kfind_ranges. apply Forall_forall. intros r Hr.
  apply in_flat_map in Hr as (K & Hin & Hr). destruct K as [ | | | | |e' lo hi| | | | ]; try (destruct Hr; fail); try contradiction.
  destruct (expr_eqb e' e) eqn:He; [|destruct Hr]. destruct Hr as [<-|[]]. apply expr_eqb_eq in He. subst e'. cbn.
  exact (hb_range E cs R FULL model e lo hi HC Hin).
Qed.
End Generic.

(* [comment removed for export] *)
Ltac hb_linZ :=
  unfold LZ;
  repeat (match goal with |- context [lin_of ?e] => let l := eval vm_compute in (lin_of e) in change (lin_of e) with l end);
  cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE edenot];
  repeat (match goal with |- context [bv_unsigned (ev ?E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) end);
  rewrite ?Z.add_0_r.

(* [comment removed for export] *)
Ltac hb_in := apply hb_knb_In; vm_compute; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Image.
Variable SEGS : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Hypothesis IMG : img_facts SEGS A ph.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
(* [comment removed for export] *)
Variable HSf : nat -> option acs.
Variable HSc : nat -> acs.
Hypothesis HSf_some : forall h, (h < 2)%nat -> HSf h = Some (HSc h).
Hypothesis HSf_none : forall h, (2 <= h)%nat -> HSf h = None.
(* [comment removed for export] *)
Hypothesis NOFOG : forall h, (h < 2)%nat -> no_fog (a_maps (HSc h)) = true.
Hypothesis MAPSLIN : forall h, (h < 2)%nat -> amaps_lin (kn (HSc h)) (a_maps (HSc h)) = true.
Hypothesis VISLIN : forall h, (h < 2)%nat -> vis_lin (kn (HSc h)) (a_vis (HSc h) ++ a_ghost (HSc h)) = true.
Hypothesis BRKLIN : forall h, (h < 2)%nat -> lin_nowrapR (kn (HSc h)) (a_brk (HSc h)) = true.
Hypothesis FDSTD : forall h, (h < 2)%nat -> a_fd (HSc h) = FdStd.
(* [comment removed for export] *)
(* [comment removed for export] *)
Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs).   (* [comment removed for export] *)
Variable stdin : InputStream.
Variable gid : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abrt : bool.
Variable ur : InputStream.
Variable kb : KernelBuild.
Variable execfn : list byte.
Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
Variable apc : N.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk SEGS brk0.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
  (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
#[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation CSOK := (cs_ok SEGS A AsanInitK.LIMIT SINV argH fs).

Let argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a :=
  argH0_high sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva.

(* [comment removed for export] *)
Lemma hbi_ch : forall h ch, HSf h = Some ch -> ch = HSc h /\ (h < 2)%nat.
Proof.
  intros h ch H. destruct (Nat.lt_ge_cases h 2) as [Hl|Hl].
  - rewrite (HSf_some h Hl) in H. injection H as <-. auto.
  - rewrite (HSf_none h Hl) in H. discriminate.
Qed.

(* [comment removed for export] *)
Definition MAPS (h : nat) (E : env) : list (word * word) := map (amap_den E) (a_maps (HSc h)).

Lemma hbi_maps : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  vm_maps (m_vmmaps model) = MAPS h E.
Proof. intros h E R FULL model Hh HC. exact (hb_maps SEGS A _ _ _ _ E _ R FULL model HC (NOFOG h Hh)). Qed.

Lemma hbi_maps_Z : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  map (fun e => (B e, B e + S e)) (vm_maps (m_vmmaps model)) = map (amapZ E) (a_maps (HSc h)).
Proof. intros h E R FULL model Hh HC. exact (hb_maps_Z SEGS A _ _ _ _ E _ R FULL model HC (NOFOG h Hh) (MAPSLIN h Hh)). Qed.

Lemma hbi_maps_len : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  length (vm_maps (m_vmmaps model)) = length (a_maps (HSc h)).
Proof. intros h E R FULL model Hh HC. rewrite (hbi_maps h E R FULL model Hh HC). apply length_map. Qed.

Lemma hbi_brkZ : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  bv_unsigned (vm_brk (m_vmmaps model)) = LZ E (a_brk (HSc h)).
Proof. intros h E R FULL model Hh HC. exact (hb_brkZ SEGS A _ _ _ _ E _ R FULL model HC (BRKLIN h Hh)). Qed.

Lemma hbi_allowA_Z : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  allowA A E (HSc h) = flat_map (allow1Z A E) (a_vis (HSc h) ++ a_ghost (HSc h)).
Proof. intros h E R FULL model Hh HC. exact (hb_allowA_Z SEGS A _ _ _ _ E _ R FULL model HC (VISLIN h Hh)). Qed.

Lemma hbi_fds : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model -> m_fds model = fds_std.
Proof. intros h E R FULL model Hh HC. exact (hb_fds_std SEGS A _ _ _ _ E _ R FULL model HC (FDSTD h Hh)). Qed.

(* [comment removed for export] *)
Lemma hbi_E0 : forall E cs R FULL model, CSOK E cs R FULL model ->
  forall n, (n < NX0)%nat -> ev E n = ev (E0 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) n.
Proof. intros E cs R FULL model HC. exact (proj1 (hb_sinv SEGS A _ _ _ _ E cs R FULL model HC)). Qed.

#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
(* [comment removed for export] *)
#[local] Notation INP := (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
#[local] Notation rseq := (kb_rseq (in_kernel INP)).
#[local] Notation top := (ed_top rdraw).
#[local] Notation utop := (bv_unsigned top).
#[local] Notation entryw := (Z_to_bv 64 (Z.of_N apc)).
#[local] Notation STR0 := (usp + Z.of_nat (cat_string_off rseq sp top argv envp execfn)).
(* [comment removed for export] *)
Definition Wsb : Z := Z.of_nat (block_pad_len rseq sp top argv envp execfn).

Lemma hbi_vals : forall E cs R FULL model, CSOK E cs R FULL model ->
  VZ E 0 (* [comment removed for export] *) = usp / 32768 /\ VZ E 6 (* [comment removed for export] *) = (usp mod 4096) / 16
  /\ VZ E 1 (* [comment removed for export] *) = argc /\ VZ E 2 (* [comment removed for export] *) = envc
  /\ VZ E 3 (* [comment removed for export] *) = Z.of_nat (length (nth 0 argv [])) /\ VZ E 7 (* [comment removed for export] *) = Z.of_nat (length (nth 1 argv []))
  /\ VZ E 4 (* [comment removed for export] *) = Wsb /\ VZ E 5 (* [comment removed for export] *) = bv_unsigned brk0 / 4096 /\ ev E 8 (* [comment removed for export] *) = uid
  /\ ev E 9 (* [comment removed for export] *) = hw /\ VZ E 10 (* [comment removed for export] *) = (usp mod 32768) / 4096.   (* [comment removed for export] *)
Proof.
  intros E cs R FULL model HC. pose proof (hbi_E0 E cs R FULL model HC) as HE.
  pose proof (uE0 ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
  pose proof (uE0_L1 sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hva) as U8.
  pose proof (uE0_s2a ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau) as U9.
  unfold APSK.uE in *. cbn [edenot] in U1, U2, U3, U4, U5, U6, U7, U8, U9.
  unfold V_S1, V_S2, V_S2A, V_ARGC, V_ENVC, V_L0, V_L1, V_W, V_BRK, V_UID, V_HW in *. unfold VZ. rewrite !HE by (unfold NX0; lia).
  repeat split; try assumption; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hbi_sp0 : forall E cs R FULL model, CSOK E cs R FULL model -> 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
Proof.
  intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (U1 & U2 & _ & _ & _ & _ & _ & _ & _ & _ & U3). rewrite U1, U2, U3.
  pose proof Hsp as (_ & _ & Hal). pose proof (u64_range sp).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma hbi_sppg : forall E cs R FULL model, CSOK E cs R FULL model -> 32768 * VZ E 0 + 4096 * VZ E 10 = usp / 4096 * 4096.
Proof.
  intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (U1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & U3). rewrite U1, U3.
  pose proof Hsp as (_ & _ & Hal). pose proof (u64_range sp).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma hbi_brk0 : forall E cs R FULL model, CSOK E cs R FULL model -> 4096 * VZ E 5 = bv_unsigned brk0.
Proof.
  intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (_ & _ & _ & _ & _ & _ & _ & U & _). rewrite U.
  pose proof (brk_range SEGS A ph sp rdraw brk0 argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc IMG Hbrk) as [_ Hm].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma hbi_sp_range : sp_window_lo <= usp <= sp_window_hi /\ usp mod 16 = 0.
Proof. pose proof Hsp as (H1 & H2 & H3). auto. Qed.

(* [comment removed for export] *)
Lemma hbi_argblock : forall E cs R FULL model, CSOK E cs R FULL model ->
  forall a : word, argH E a = true -> FULL a = wrap_mem INP mbase ph entryw sp rdraw a.
Proof. intros E cs R FULL model HC. exact (proj2 (hb_sinv SEGS A _ _ _ _ E cs R FULL model HC)). Qed.

(* [comment removed for export] *)
Lemma hbi_argH : forall E (a : word),
  argH E a = ((uE E e_sp0 <=? bv_unsigned a) &&
              (((usp + 24 <=? bv_unsigned a) && (bv_unsigned a <? usp + 8 * argc + 8 * envc + 24))
              || ((STR0 <=? bv_unsigned a) && (bv_unsigned a <? utop))))%bool.
Proof. reflexivity. Qed.
End Image.
End HandoffBridgeK.
Module HandoffLedgerK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hl_covered_in_ivs : forall l z, BackingAlgebra.covered l z = in_ivs z l.
Proof. intros l z. unfold BackingAlgebra.covered, in_ivs. induction l as [|q l IH]; [reflexivity|]. cbn [existsb]. rewrite IH. reflexivity. Qed.

Lemma hl_seps_apart : forall l, seps l ->
  forall q q', In q l -> In q' l -> q <> q' ->
    BackingAlgebra.B q + BackingAlgebra.S q <= BackingAlgebra.B q' \/ BackingAlgebra.B q' + BackingAlgebra.S q' <= BackingAlgebra.B q.
Proof.
  intros l Hs. induction Hs as [|p l Hp Hs IH]; intros q q' Hq Hq' Hne; [destruct Hq|].
  unfold BackingAlgebra.B, BackingAlgebra.S in *.
  destruct Hq as [<-|Hq]; destruct Hq' as [<-|Hq'].
  - congruence.
  - exact (proj1 (Forall_forall _ _) Hp q' Hq').
  - pose proof (proj1 (Forall_forall _ _) Hp q Hq) as D. unfold iv_disjoint in D. lia.
  - exact (IH q q' Hq Hq' Hne).
Qed.

Lemma hl_seps_nodup : forall l, seps l -> (forall q, In q l -> 0 < bv_unsigned (snd q)) -> List.NoDup l.
Proof.
  intros l Hs. induction Hs as [|p l Hp Hs IH]; intros Hpos; [constructor|].
  constructor.
  - intros Hin. pose proof (proj1 (Forall_forall _ _) Hp p Hin) as D. unfold iv_disjoint in D.
    pose proof (Hpos p (or_introl eq_refl)). lia.
  - apply IH. intros q Hq. apply Hpos. right. exact Hq.
Qed.

(* [comment removed for export] *)
Lemma hl_iv_subtract : forall (a sz : word) lo hi q,
  bv_unsigned a + bv_unsigned sz <= 2 ^ 64 -> 0 < bv_unsigned sz ->
  In q (iv_subtract a sz lo hi) ->
  0 < bv_unsigned (snd q) /\ bv_unsigned a <= bv_unsigned (fst q)
  /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi q Hwf Hpos Hin. unfold iv_subtract in Hin.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma hl_maps_subtract : forall l lo hi q,
  (forall p, In p l -> bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64 /\ 0 < bv_unsigned (snd p)) ->
  In q (maps_subtract l lo hi) ->
  0 < bv_unsigned (snd q)
  /\ exists p, In p l /\ bv_unsigned (fst p) <= bv_unsigned (fst q)
               /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p) + bv_unsigned (snd p).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hl Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
  - destruct (Hl (a, sz) (or_introl eq_refl)) as [W P]. cbn [fst snd] in W, P.
    destruct (hl_iv_subtract a sz lo hi q W P Hin) as (Q1 & Q2 & Q3).
    split; [exact Q1|]. exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. lia.
  - destruct (IH lo hi q (fun p Hp => Hl p (or_intror Hp)) Hin) as (Q1 & p & Hp & Q2 & Q3).
    split; [exact Q1|]. exists p. split; [right; exact Hp|]. lia.
Qed.

(* [comment removed for export] *)
Lemma hl_replay : forall E h,
  (forall b n, In (HCons b n) h -> uE E b + uE E n <= 2 ^ 64 /\ 0 < uE E n) ->
  forall q, In q (hreplay E h) ->
    0 < bv_unsigned (snd q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64
    /\ exists b n, In (HCons b n) h /\ uE E b <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= uE E b + uE E n.
Proof.
  intros E h. induction h as [|hop h IH]; intros Hh q Hin; [destruct Hin|].
  destruct hop as [b n|b n]; cbn [hreplay] in Hin.
  - destruct Hin as [<-|Hin].
    + destruct (Hh b n (or_introl eq_refl)) as [W P]. cbn [fst snd]. unfold uE in *.
      split; [exact P|]. split; [exact W|]. exists b, n. split; [left; reflexivity|]. lia.
    + destruct (IH (fun b' n' H' => Hh b' n' (or_intror H')) q Hin) as (Q1 & Q2 & b' & n' & Hb & Q3 & Q4).
      split; [exact Q1|]. split; [exact Q2|]. exists b', n'. split; [right; exact Hb|]. lia.
  - assert (IH' := IH (fun b' n' H' => Hh b' n' (or_intror H'))).
    destruct (hl_maps_subtract (hreplay E h) _ _ q (fun p Hp => let '(conj P1 (conj P2 _)) := IH' p Hp in conj P2 P1) Hin) as (Q1 & p & Hp & Q2 & Q3).
    destruct (IH' p Hp) as (P1 & P2 & b' & n' & Hb & P3 & P4).
    split; [exact Q1|]. split; [lia|]. exists b', n'. split; [right; exact Hb|]. lia.
Qed.

(* [comment removed for export] *)
Lemma hl_in_amapb : forall m ms, existsb (amap_eqb m) ms = true -> In m ms.
Proof. intros m ms H. apply existsb_exists in H as (m' & Hin & Heq). apply amap_eqb_eq in Heq. subst m'. exact Hin. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition len_within (n len : expr) : bool :=
  (expr_eqb len n || match n, len with ELit z, ELit L => (Z.ltb 0 z && Z.leb z L && Z.ltb L (2 ^ 64))%bool | _, _ => false end)%bool.
Definition hop_in_maps (ms : list amap) (hp : hop) : bool :=
  match hp with
  | HCons b n => existsb (fun m => negb (is_fog m) && expr_eqb (am_base m) b && len_within n (am_len m))%bool ms   (* [comment removed for export] *)
  | HSub _ _ => true
  end.
Definition hops_in_maps (ms : list amap) (h : list hop) : bool := forallb (hop_in_maps ms) h.

Section Ledger.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (hid A argH).
(* [comment removed for export] *)
Let HSd : nat -> option acs := fun _ => None.
Let XNd : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XEd : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XBd : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
#[local] Notation PIRI := (page_in_ranges_In HSd XNd XEd XBd 0%nat).
#[local] Notation PBLE := (page_base_le HSd XNd XEd XBd 0%nat).

Lemma hl_alloc_top : forall E cs R FULL model, CSOK E cs R FULL model ->
  alloc_top (m_vmmaps model) = uE E e_sp0 - 8388608.
Proof.
  intros E cs R FULL model HC. destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (H1 & _). unfold alloc_top, stack_max_size. rewrite H1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hl_maps_pos : forall E cs R FULL model q, CSOK E cs R FULL model -> In q (vm_maps (m_vmmaps model)) ->
  0 < bv_unsigned (snd q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= uE E e_sp0 - 8388608.
Proof.
  intros E cs R FULL model q HC Hin.
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) q Hin) as (P1 & _ & _ & _ & P5).
  pose proof (utop_bounds E). split; [exact P1 | lia].
Qed.

(* [comment removed for export] *)
Lemma hl_hop_in_maps : forall E cs R FULL model h, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) h = true ->
  forall b n, In (HCons b n) h ->
    exists q, In q (vm_maps (m_vmmaps model)) /\ fst q = edenot E b /\ 0 < uE E n <= bv_unsigned (snd q).
Proof.
  intros E cs R FULL model h HC Hnf Hh b n Hin.
  pose proof (proj1 (forallb_forall _ _) Hh _ Hin) as Hb. cbn [hop_in_maps] in Hb.
  apply existsb_exists in Hb as (m & Hm & Hb). apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [_ Hb].
  apply expr_eqb_eq in Hb. subst b.
  assert (Hq : In (amap_den E m) (vm_maps (m_vmmaps model))).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply in_map_iff. exists m. split; [reflexivity | exact Hm]. }
  exists (amap_den E m). split; [exact Hq|]. split; [reflexivity|].
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hq) as (P1 & _).
  unfold amap_den in *. cbn [fst snd] in *. unfold len_within in Hn. apply orb_prop in Hn as [Hn|Hn].
  - apply expr_eqb_eq in Hn. rewrite <- Hn. unfold uE. lia.
  - destruct n as [z|n0|o a1 a2|o a1 a2|o a1 a2|o a1 a2|sx lo0 n0 e0|sx k0 i0 n0]; try discriminate.
    destruct (am_len m) as [L|n1|o b1 b2|o b1 b2|o b1 b2|o b1 b2|sx lo1 n1 e1|sx k1 i1 n1]; try discriminate.
    apply andb_prop in Hn as [Hn H3]. apply andb_prop in Hn as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    unfold uE. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.

Lemma hl_hops_ok : forall E cs R FULL model h, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) h = true ->
  forall b n, In (HCons b n) h -> uE E b + uE E n <= 2 ^ 64 /\ 0 < uE E n.
Proof.
  intros E cs R FULL model h HC Hnf Hh b n Hin.
  destruct (hl_hop_in_maps E cs R FULL model h HC Hnf Hh b n Hin) as (q & Hq & Hb & Hn).
  destruct (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W & _).
  pose proof (W _ Hq) as Wq. unfold BackingAlgebra.iv_wf, BackingAlgebra.B, BackingAlgebra.S in Wq. rewrite Hb in Wq. unfold uE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma hl_noacc_pos : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) (a_hna cs) = true ->
  forall q, In q (vm_noaccess (m_vmmaps model)) -> 0 < bv_unsigned (snd q).
Proof.
  intros E cs R FULL model HC Hnf Hh q Hin. rewrite (co_hna _ _ _ _ _ _ _ _ _ _ _ HC) in Hin.
  exact (proj1 (hl_replay E (a_hna cs) (hl_hops_ok E cs R FULL model _ HC Hnf Hh) q Hin)).
Qed.

(* [comment removed for export] *)
Lemma hl_lazy_in : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) (a_hlz cs) = true ->
  forall a : word, page_in_ranges (page_base a) (m_vm_lazy model) = true ->
    in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true /\ find_segment SEGS (bv_unsigned a) 1 = None.
Proof.
  intros E cs R FULL model HC Hnf Hh a Hp.
  destruct (PIRI a _ Hp) as (iv & Hiv & B1 & B2 & _ & _).
  split.
  - rewrite (co_hlz _ _ _ _ _ _ _ _ _ _ _ HC) in Hiv.
    destruct (hl_replay E (a_hlz cs) (hl_hops_ok E cs R FULL model _ HC Hnf Hh) iv Hiv) as (_ & _ & b & n & Hb & Q1 & Q2).
    destruct (hl_hop_in_maps E cs R FULL model _ HC Hnf Hh b n Hb) as (q & Hq & Hqb & Hqn).
    unfold in_ivs. apply existsb_exists. exists q. split; [exact Hq|]. rewrite Hqb. unfold uE in *.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - apply SEGS_in_hull.
    pose proof (proj1 (Forall_forall _ _) (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC) iv Hiv) as [L1 _].
    unfold in_hull. destruct L1 as [L1|L1]; apply andb_false_iff; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.

(* [comment removed for export] *)
Lemma hl_hidden_zero : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  hops_in_maps (a_maps cs) (a_hlz cs) = true ->
  forall a : word, mkH (m_vm_lazy model) (allowA A E cs) a = true ->
    in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
    FULL a = Some (Z_to_bv 8 0).
Proof.
  intros E cs R FULL model HC Hnf Hh a Hm Hna. unfold mkH in Hm. apply andb_prop in Hm as [Hlz Hal]. apply negb_true_iff in Hal.
  destruct (hl_lazy_in E cs R FULL model HC Hnf Hh a Hlz) as [Hin _].
  (* [comment removed for export] *)
  assert (Hhid : HID E cs model a = true).
  { destruct (HID E cs model a) eqn:Hh'; [reflexivity|]. exfalso.
    pose proof (lazy_cover_cs SEGS A LIMIT HSd XNd XEd XBd HULL_ok SINV argH FS0 0%nat E cs R FULL model HC a Hlz Hh') as Hc. congruence. }
  apply (hb_zero SEGS A LIMIT SINV argH FS0 E cs R FULL model a HC Hhid Hin Hna Hlz).
  (* [comment removed for export] *)
  destruct (in_ghost E cs (bv_unsigned a)) eqn:Hg; [exfalso | reflexivity].
  unfold in_ghost in Hg. apply existsb_exists in Hg as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
  apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  assert (Hc : page_allowedb (allowA A E cs) (page_base a) = true); [|congruence].
  pose proof (PBLE a) as (P1 & P2 & P3).
  unfold page_allowedb, allowA. apply existsb_exists.
  exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
  - apply in_flat_map. exists p. split; [apply in_or_app; right; exact Hp|]. left. reflexivity.
  - cbn [fst snd]. unfold page_size.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHB_LO : Z := 0x7fff7000.
Definition SHB_LEN : Z := 0x100000001000.

(* [comment removed for export] *)
Definition vis_sh_wr (k : list kentry) (p : expr * expr) : bool :=
  let '(sb, sk, sn) := shadow_of A k (fst p) (snd p) in
  (Z.leb 3 (ealign k (fst p)) && flat_x k sb sk sn && existsb (kentry_eqb (KWr (SA sb sk) sn)) k)%bool.
Definition vis_off_band (k : list kentry) (p : expr * expr) : bool :=
  let '(bb, bk) := split_lit (fst p) in
  (flat_x k bb bk (snd p) && ranges_apart_x k (ELit SHB_LO) 0 (ELit SHB_LEN) bb bk (snd p))%bool.

Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis HULL_below : img_hi A <= SHB_LO.

Lemma hl_off_band : forall E cs R FULL model p z, CSOK E cs R FULL model -> vis_off_band (kn cs) p = true ->
  uE E (fst p) <= z < uE E (fst p) + uE E (snd p) -> ~ (SHB_LO <= z < SHB_LO + SHB_LEN).
Proof.
  intros E cs R FULL model p z HC Hv Hz Hband. unfold vis_off_band in Hv.
  destruct (split_lit (fst p)) as [bb bk] eqn:Hsp. apply andb_prop in Hv as [Hf Hap].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) bb bk (snd p) HK Hf) as (F1 & F2 & F3).
  pose proof (split_lit_denot E _ bb bk Hsp) as Hd.
  assert (Hb : uE E (fst p) = estart E (SA bb bk)).
  { unfold uE. rewrite Hd. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
  unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
  unfold SHB_LO, SHB_LEN in *. rewrite !u64_lit in D by lia. unfold uE in *. lia.
Qed.

Lemma hl_shadow_defined : forall E cs R FULL model, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  forallb (vis_sh_wr (kn cs)) (a_vis cs) = true ->
  forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true ->
  forall m BL LL, In m (a_maps cs) -> am_kind m = KRWLAZY -> am_base m = ELit BL -> am_len m = ELit LL ->
    SHB_LO <= BL -> 0 <= LL -> BL + LL <= SHB_LO + SHB_LEN ->
  forall a : word, BL <= bv_unsigned a < BL + LL -> FULL a <> None.
Proof.
  intros E cs R FULL model HC Hnf Hwr Hoff m BL LL Hm Hk Hbase Hlen HB HL HBL a Ha.
  unfold SHB_LO, SHB_LEN in *.
  assert (Hden : bv_unsigned (edenot E (am_base m)) = BL /\ bv_unsigned (edenot E (am_len m)) = LL).
  { rewrite Hbase, Hlen. cbn [edenot]. rewrite !u64_lit by lia. auto. }
  destruct Hden as [D1 D2].
  destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model m a HC Hm Hk ltac:(rewrite D1, D2; exact Ha)) as [Hna Hlz].
  assert (Hin : in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). unfold in_ivs. apply existsb_exists.
    exists (amap_den E m). split; [apply in_map; exact Hm|]. unfold amap_den. cbn [fst snd]. rewrite D1, D2.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  pose proof (proj1 (forallb_forall _ _) Hoff) as Hoff'.
  destruct (HID E cs model a) eqn:Hh.
  - (* [comment removed for export] *)
    assert (Hg : in_ghost E cs (bv_unsigned a) = false).
    { destruct (in_ghost E cs (bv_unsigned a)) eqn:Hg; [exfalso | reflexivity].
      unfold in_ghost in Hg. apply existsb_exists in Hg as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      apply (hl_off_band E cs R FULL model p (bv_unsigned a) HC (Hoff' p (in_or_app _ _ _ (or_intror Hp))) (conj Hb1 Hb2)).
      unfold SHB_LO, SHB_LEN. lia. }
    rewrite (hb_zero SEGS A LIMIT SINV argH FS0 E cs R FULL model a HC Hh Hin Hna Hlz Hg). discriminate.
  - (* [comment removed for export] *)
    rewrite hb_hid_unfold in Hh. apply orb_false_iff in Hh as [_ Hv]. apply negb_false_iff in Hv. unfold vis in Hv.
    pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
    destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & (SPlo & _) & _).
    pose proof (utop_bounds E) as UT. unfold sp_window_lo in SPlo.
    apply orb_prop in Hv as [Hv|Hv].
    { exfalso. apply orb_prop in Hv as [Hv|Hv].
      - unfold in_hull in Hv. apply andb_prop in Hv as [_ Hv]. apply Z.ltb_lt in Hv. lia.
      - apply Z.leb_le in Hv. lia. }
    apply andb_prop in Hv as [_ Hv]. rewrite Hlz in Hv. cbn [negb orb] in Hv. unfold in_allow in Hv.
    apply orb_prop in Hv as [Hv|Hv].
    { exfalso. unfold in_vis in Hv. apply existsb_exists in Hv as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
      apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      apply (hl_off_band E cs R FULL model p (bv_unsigned a) HC (Hoff' p (in_or_app _ _ _ (or_introl Hp))) (conj Hb1 Hb2)).
      unfold SHB_LO, SHB_LEN. lia. }
    unfold in_sh in Hv. apply existsb_exists in Hv as [p [Hp Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
    pose proof (proj1 (forallb_forall _ _) Hwr p Hp) as Hw. unfold vis_sh_wr in Hw.
    destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hso.
    apply andb_prop in Hw as [Hw Hkw]. apply andb_prop in Hw as [Hal Hfl]. apply Z.leb_le in Hal.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (shadow_of_val SEGS A SHADOW_ok E _ (kn cs) (fst p) (snd p) sb sk sn HK Hso Hfl) as [S1 S2].
    destruct (ealign_sound SEGS E _ (kn cs) (fst p) HK) as [[A0 A1] [q Hq]].
    assert (H8 : exists q8, bv_unsigned (edenot E (fst p)) = 8 * q8).
    { exists (q * 2 ^ (ealign (kn cs) (fst p) - 3)). rewrite Hq.
      replace (2 ^ ealign (kn cs) (fst p)) with (2 ^ (ealign (kn cs) (fst p) - 3) * 2 ^ 3) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      change (2 ^ 3) with 8. ring. }
    destruct H8 as [q8 H8].
    apply existsb_exists in Hkw as (K & HKin & HKeq). apply kentry_eqb_eq in HKeq. subst K.
    pose proof (proj1 (Forall_forall _ _) HK _ HKin) as HKW. cbn [kentry_ok] in HKW. destruct HKW as [Hflat HKW].
    pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
    pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
    unfold sh_lo, sh_hi, uE in Hb1, Hb2. rewrite H8 in Hb1, Hb2, S1.
    assert (E1 : 8 * q8 / 8 = q8) by (rewrite Z.mul_comm; apply Z.div_mul; lia).
    assert (E2 : (8 * q8 + bv_unsigned (edenot E (snd p))) / 8 = q8 + bv_unsigned (edenot E (snd p)) / 8).
    { rewrite Z.add_comm, Z.mul_comm. rewrite Z.div_add by lia. lia. }
    rewrite E1 in Hb1, S1. rewrite E2 in Hb2.
    assert (Hq8 : 0 <= q8 < 2 ^ 61) by lia.
    rewrite Z.mod_small in S1 by lia.
    set (d := bv_unsigned a - estart E (SA sb sk)).
    assert (Hd : 0 <= d /\ d + Z.of_nat 1 <= elenZ E sn) by (unfold d; rewrite S1, S2; lia).
    pose proof (HKW d 1%nat (proj1 Hd) (proj2 Hd)) as Hst.
    replace (Z_to_bv 64 (estart E (SA sb sk) + d)) with a in Hst
      by (unfold d; replace (estart E (SA sb sk) + (bv_unsigned a - estart E (SA sb sk))) with (bv_unsigned a) by ring; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (hb_mr_store_ok SEGS A argH SEGS_in_hull HULL_ok argH_high E cs model FULL a 1 Hst) as [Hst' _].
    cbn [store_ok] in Hst'. unfold wview in Hst'. intros Hnone. rewrite Hnone in Hst'.
    rewrite (SEGS_in_hull a) in Hst'; [discriminate|].
    unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
End Ledger.

End HandoffLedgerK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.
Module HandoffBInvK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.AsanPlacement OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.AsanCeil OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma hl_minv_mono : forall A A' m, MInv A m ->
  (forall p, page_allowedb A p = true -> page_allowedb A' p = true) ->
  eager_used m + A_bytes A' <= vm_limit (m_vmmaps m) -> MInv A' m.
Proof.
  intros A A' m [N1 N2 N3 N4 N5] Hsub Hb. constructor; try assumption. intros p Hp. apply Hsub. exact (N3 p Hp).
Qed.

Lemma hl_A_bytes_app : forall A B, A_bytes (A ++ B) = A_bytes A + A_bytes B.
Proof. induction A as [|iv A IH]; intros B; cbn [A_bytes app]; [lia | rewrite IH; lia]. Qed.

Lemma hl_sum_gw : forall l, sum_sizes l = AsanPlacement.gw_sizes l.
Proof. induction l as [|q l IH]; [reflexivity|]. cbn [sum_sizes AsanPlacement.gw_sizes]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition M_LOW : amap := {| am_base := ELit 0x7fff7000; am_len := ELit 0x10000000; am_kind := KRWLAZY |}.
Definition M_GAP : amap := {| am_base := ELit 0x8fff7000; am_len := ELit 0x20000000000; am_kind := KNONELAZY |}.
Definition M_HIGH : amap := {| am_base := ELit 0x2008fff7000; am_len := ELit 0xdfff0001000; am_kind := KRWLAZY |}.

Section BInvMain.
Variable SEGS : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis IMG : img_facts SEGS A ph.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis HULL_below : img_hi A <= SHB_LO.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS).
Hypothesis RESV_pos : forall b s, In (b, s) (segments_reserved SEGS) -> 0 < bv_unsigned s.

(* [comment removed for export] *)
Variable cs : acs.
Hypothesis NOFOG : no_fog (a_maps cs) = true.
Hypothesis HNA : hops_in_maps (a_maps cs) (a_hna cs) = true.
Hypothesis HLZ : hops_in_maps (a_maps cs) (a_hlz cs) = true.
Hypothesis VWR : forallb (vis_sh_wr A (kn cs)) (a_vis cs) = true.
Hypothesis VOFF : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true.
Hypothesis IN_LOW : In M_LOW (a_maps cs).
Hypothesis IN_GAP : In M_GAP (a_maps cs).
Hypothesis IN_HIGH : In M_HIGH (a_maps cs).
(* [comment removed for export] *)
Variable RESm : list amap.
Hypothesis RESm_in : forall m, In m RESm -> In m (a_maps cs).
Hypothesis RESm_pos : forall m, In m RESm -> exists lo, xlo (kn cs) (am_base m) = Some lo /\ 0 < lo.

(* [comment removed for export] *)
Variables BUDGET LENMAX KMAX : Z.
Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
Variable EXTRA : list (Z * Z).
Hypothesis EXTRA_wf : A_wf EXTRA.
Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= LIMIT.
(* [comment removed for export] *)
Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                 + (Z.of_nat (length (segments_reserved SEGS) + n_resx A + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

Definition resZ (E : env) (m : amap) : Z * Z := (uE E (am_base m), uE E (am_len m)).
Definition RES_of (E : env) : list (Z * Z) := map (resZ E) RESm.
Definition BASE_of : Z := a_eager cs + a_abytes cs + A_bytes EXTRA.
Definition A0_of (E : env) : list (Z * Z) := allowA A E cs ++ EXTRA.

Section Run.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : CSOK E cs R FULL model.

#[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
(* [comment removed for export] *)
#[local] Notation RESV0 := (vm_reserved (m_vmmaps model)).
#[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
#[local] Notation CEIL0 := (uE E e_sp0 - 8388608).

Let Hmaps := hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC NOFOG.

Lemma hb_in_maps : forall m, In m (a_maps cs) -> In (amap_den E m) MAPS0.
Proof. intros m Hm. rewrite Hmaps. apply in_map. exact Hm. Qed.

Lemma hb_sp0_window : sp_window_lo <= uE E e_sp0 <= sp_window_hi.
Proof. exact (proj1 (proj2 (co_isp _ _ _ _ _ _ _ _ _ _ _ HC))). Qed.

(* [comment removed for export] *)
Lemma hb_lit_covered : forall m BL LL x, In m (a_maps cs) -> am_base m = ELit BL -> am_len m = ELit LL -> 0 <= BL -> 0 <= LL -> BL + LL < 2 ^ 64 ->
  BL <= x < BL + LL -> BackingAlgebra.covered MAPS0 x = true.
Proof.
  intros m BL LL x Hm Hb Hl H0 H1 H2 Hx. rewrite hl_covered_in_ivs. unfold in_ivs. apply existsb_exists.
  exists (amap_den E m). split; [exact (hb_in_maps m Hm)|]. unfold amap_den. cbn [fst snd]. rewrite Hb, Hl. cbn [edenot].
  rewrite !u64_lit by lia. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma hb_lit_entry : forall m BL LL lo hi, In m (a_maps cs) -> am_base m = ELit BL -> am_len m = ELit LL -> 0 <= BL -> 0 <= LL -> BL + LL < 2 ^ 64 ->
  BL <= lo -> hi <= BL + LL ->
  exists b s, In (b, s) MAPS0 /\ bv_unsigned b <= lo /\ hi <= bv_unsigned b + bv_unsigned s.
Proof.
  intros m BL LL lo hi Hm Hb Hl H0 H1 H2 Hlo Hhi. exists (edenot E (am_base m)), (edenot E (am_len m)).
  split; [exact (hb_in_maps m Hm)|]. rewrite Hb, Hl. cbn [edenot]. rewrite !u64_lit by lia. lia.
Qed.

Lemma hb_shrw_facts : forall x, in_shadow_rw x ->
  img_hi A <= x /\ in_ivs x NOACC0 = false.
Proof.
  intros x Hx. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx. unfold SHB_LO in HULL_below. split; [lia|].
  assert (Hw : 0 <= x < 2 ^ 64) by lia.
  destruct Hx as [Hx|Hx].
  - destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model M_LOW (Z_to_bv 64 x) HC IN_LOW eq_refl) as [Hn _].
    + cbn [M_LOW am_base am_len edenot]. rewrite !u64_lit by lia. lia.
    + rewrite u64_lit in Hn by lia. exact Hn.
  - destruct (hb_lazykind SEGS A LIMIT SINV argH FS0 E cs R FULL model M_HIGH (Z_to_bv 64 x) HC IN_HIGH eq_refl) as [Hn _].
    + cbn [M_HIGH am_base am_len edenot]. rewrite !u64_lit by lia. lia.
    + rewrite u64_lit in Hn by lia. exact Hn.
Qed.

Theorem hb_bridge_static : bridge_static SEGS MAPS0 RESV0 NOACC0 (RES_of E) CEIL0 BUDGET LENMAX KMAX.
Proof.
  pose proof hb_sp0_window as [SPlo SPhi]. unfold sp_window_lo, sp_window_hi in *.
  pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (HU0 & HU1 & HU2 & HU3).
  unfold SHB_LO in HULL_below.
  constructor.
  - exact (proj1 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)).
  - intros q Hq. exact (proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq)).
  - (* [comment removed for export] *)
    destruct (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as (rx & Hres & HG & _ & _).
    intros b s Hbs. rewrite Hres in Hbs. apply in_app_iff in Hbs as [Hbs|Hbs].
    + exact (RESV_pos b s Hbs).
    + exact (proj1 (proj1 (Forall_forall _ _) HG _ Hbs)).
  - apply hl_seps_nodup; [exact (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)|].
    intros q Hq. exact (proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq)).
  - exact (hl_seps_apart _ (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)).
  - intros x Hx. destruct (hb_shrw_facts x Hx) as [Hh _].
    assert (Hw : 0 <= x < 2 ^ 64) by (unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx; lia).
    pose proof (SEGS_in_hull (Z_to_bv 64 x)) as Hs. rewrite u64_lit in Hs by lia. apply Hs.
    unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  - (* [comment removed for export] *)
    intros Rz HR. unfold RES_of in HR. apply in_map_iff in HR as (m & <- & Hm).
    pose proof (hb_in_maps m (RESm_in m Hm)) as Hin.
    destruct (RESm_pos m Hm) as (lo & Hlo & Hpos).
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hlo) as Hb.
    destruct (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model _ HC Hin) as [P1 P2]. unfold amap_den in P1, P2. cbn [fst snd] in P1, P2.
    unfold resZ, toW. cbn [fst snd]. unfold uE. rewrite !Z_to_bv_bv_unsigned.
    split; [exact Hin|]. pose proof (u64_range (edenot E (am_base m))). pose proof (u64_range (edenot E (am_len m))). unfold uE in *. lia.
  - (* [comment removed for export] *)
    intros Rz b s HR Hbs. unfold RES_of in HR. apply in_map_iff in HR as (m & <- & Hm).
    pose proof (hb_in_maps m (RESm_in m Hm)) as Hin.
    pose proof (proj1 (Forall_forall _ _) (co_mres _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as HD.
    pose proof (proj1 (Forall_forall _ _) HD (b, s) Hbs) as D.
    unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
    unfold resZ. cbn [fst snd]. unfold uE. lia.
  - (* [comment removed for export] *)
    intros x Hx. unfold SHLO, SHHI in Hx.
    destruct (Z_lt_dec x 0x8fff7000); [|destruct (Z_lt_dec x 0x2008fff7000)].
    + apply (hb_lit_covered M_LOW _ _ x IN_LOW eq_refl eq_refl); lia.
    + apply (hb_lit_covered M_GAP _ _ x IN_GAP eq_refl eq_refl); lia.
    + apply (hb_lit_covered M_HIGH _ _ x IN_HIGH eq_refl eq_refl); lia.
  - (* [comment removed for export] *)
    intros lo hi Hlh [Hx|Hx]; unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx.
    + apply (hb_lit_entry M_LOW _ _ lo hi IN_LOW eq_refl eq_refl); lia.
    + apply (hb_lit_entry M_HIGH _ _ lo hi IN_HIGH eq_refl eq_refl); lia.
  - (* [comment removed for export] *)
    destruct (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as (rx & Hres & HG & _ & _).
    intros x b s Hx Hbs Hin. destruct (hb_shrw_facts x Hx) as [Hh _].
    unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Hx.
    rewrite Hres in Hbs. apply in_app_iff in Hbs as [Hbs|Hbs].
    + pose proof (proj1 (Forall_forall _ _) RES_hull _ Hbs) as [Q1 Q2]. cbn [fst snd] in Q1, Q2. lia.
    + pose proof (proj1 (Forall_forall _ _) HG _ Hbs) as (_ & _ & _ & _ & Hk & _).
      cbn [fst] in Hk. unfold KHI in Hk. lia.
  - (* [comment removed for export] *)
    intros x Hx. rewrite hl_covered_in_ivs. exact (proj2 (hb_shrw_facts x Hx)).
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (co_res _ _ _ _ _ _ _ _ _ _ _ HC) as (rx & Hres & _ & Hlx & _).
    assert (HL : (length RESV0 <= length (segments_reserved SEGS) + n_resx A)%nat)
      by (rewrite Hres, length_app; lia).
    rewrite <- hl_sum_gw. rewrite length_app.
    pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as Ht.
    rewrite Hmaps at 2. rewrite length_map.
    assert (0 <= LENMAX + 4095) by lia.
    assert (0 <= Z.of_nat (length RESV0) + Z.of_nat (length (a_maps cs)) + KMAX) by lia.
    rewrite !Nat2Z.inj_add in GAP. nia.
  - unfold SHHI, stack_max_size. lia.
  - exact BUD.
Qed.

Theorem hb_binv_main : BInv SEGS MAPS0 RESV0 NOACC0 CEIL0 BASE_of BUDGET [] (A0_of E) FULL model.
Proof.
  clear GAP RESm_in RESm_pos IN_GAP.
  pose proof hb_sp0_window as [SPlo SPhi]. unfold sp_window_lo, sp_window_hi in *.
  assert (Hsub : forall p, page_allowedb (allowA A E cs) p = true -> page_allowedb (A0_of E) p = true).
  { intros p Hp. unfold A0_of, page_allowedb in *. rewrite existsb_app, Hp. reflexivity. }
  pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC) as He. pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC) as Ha.
  pose proof (co_limit _ _ _ _ _ _ _ _ _ _ _ HC) as Hl.
  assert (Hbud : eager_used model + A_bytes (A0_of E) <= BASE_of) by (unfold A0_of, BASE_of; rewrite hl_A_bytes_app; lia).
  constructor.
  - exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC).
  - unfold A0_of. apply Forall_app. split; [exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs) | exact EXTRA_wf].
  - apply (hl_minv_mono (allowA A E cs)); [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hsub |]. unfold BASE_of in *. lia.
  - exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC).
  - reflexivity.
  - (* [comment removed for export] *)
    reflexivity.
  - exact (hl_alloc_top SEGS A LIMIT SINV argH FS0 E cs R FULL model HC).
  - unfold BASE_of. lia.
  - intros x Hx. exact Hx.
  - exact (hl_noacc_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model HC NOFOG HNA).
  - intros a Hp. destruct (hl_lazy_in SEGS A LIMIT SINV argH FS0 SEGS_in_hull E cs R FULL model HC NOFOG HLZ a Hp) as [H1 H2].
    rewrite hl_covered_in_ivs. split; assumption.
  - unfold live_ok. cbn. split; [intros p []|]. split; [constructor | intros p p' []].
  - intros a Hh Hna. rewrite hl_covered_in_ivs in Hna.
    apply (hl_hidden_zero SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok E cs R FULL model HC NOFOG HLZ a); [|exact Hna].
    unfold bhid, mkH in Hh |- *. apply andb_prop in Hh as [H1 H2]. rewrite H1. cbn [andb].
    apply negb_true_iff. apply negb_true_iff in H2.
    destruct (page_allowedb (allowA A E cs) (page_base a)) eqn:Hp; [|reflexivity]. rewrite (Hsub _ Hp) in H2. discriminate.
  - intros a Ha'. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI in Ha'. destruct Ha' as [Hx|Hx].
    + apply (hl_shadow_defined SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high SHADOW_ok HULL_below E cs R FULL model HC NOFOG VWR VOFF
               M_LOW 0x7fff7000 0x10000000 IN_LOW eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
    + apply (hl_shadow_defined SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high SHADOW_ok HULL_below E cs R FULL model HC NOFOG VWR VOFF
               M_HIGH 0x2008fff7000 0xdfff0001000 IN_HIGH eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
  - intros w [].
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
Qed.
End Run.
End BInvMain.
End HandoffBInvK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module HandoffCellsK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition chk_word (k : list kentry) (b : expr) (off : Z) (w : nat) (v : expr) : bool :=
  match kfind_word k b off w with Some v' => expr_eqb v' v | None => false end.

(* [comment removed for export] *)
Definition covers (b : expr) (off n : Z) (a : saddr) (len : expr) : bool :=
  match len with
  | ELit L => (expr_eqb (a_base a) b && Z.leb (a_off a) off && Z.leb (off + n) (a_off a + L) && Z.leb 0 n && Z.ltb L (2 ^ 64))%bool
  | _ => false
  end.
Definition chk_zero (k : list kentry) (b : expr) (off n : Z) : bool :=
  existsb (fun K => match K with KZero a len => covers b off n a len | _ => false end) k.
Definition chk_wr (k : list kentry) (b : expr) (off n : Z) : bool :=
  existsb (fun K => match K with KWr a len => covers b off n a len | _ => false end) k.

Definition bytes_eqb (x y : list byte) : bool :=
  (Nat.eqb (length x) (length y) && forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine x y))%bool.
Lemma bytes_eqb_eq : forall x y, bytes_eqb x y = true -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; try reflexivity; unfold bytes_eqb in H; cbn in H; try discriminate.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H2 as [H2 H3]. apply Z.eqb_eq in H2. apply bv_eq in H2. subst b. f_equal.
  apply IH. unfold bytes_eqb. rewrite H1, H3. reflexivity.
Qed.

Section Cells.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)
Definition chk_img (k : list kentry) (a : Z) (w : nat) (v : Z) : bool :=
  match kfind_img k a with
  | Some (lo, hi) =>
      (Z.leb lo a && Z.leb (a + Z.of_nat w) hi && Z.leb (img_lo A) a && Z.leb (a + Z.of_nat w) (img_hi A) && Z.leb 0 a && Z.ltb (a + Z.of_nat w) (2 ^ 64)
       && match rdn SEGS (fun _ => None) (Z_to_bv 64 a) w with
          | Some bs => bytes_eqb bs (word_to_le_bytes w (Z_to_bv 64 v))
          | None => false
          end)%bool
  | None => false
  end.

Lemma hc_word : forall E cs R FULL model b off w v,
  CSOK E cs R FULL model -> chk_word (kn cs) b off w v = true ->
  flat E (SA b off) (Z.of_nat w)
  /\ rdn SEGS FULL (Z_to_bv 64 (uE E b + off)) w = Some (word_to_le_bytes w (Z_to_bv 64 (uE E v))).
Proof.
  intros E cs R FULL model b off w v HC H. unfold chk_word in H.
  destruct (kfind_word (kn cs) b off w) as [v'|] eqn:Hk; [|discriminate]. apply expr_eqb_eq in H. subst v'.
  destruct (hb_word_at SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E cs R FULL model b off w v HC Hk) as (_ & Hf & Hr & _).
  split; [exact Hf|].
  pose proof (flat_u E _ _ Hf) as Hu. unfold estart in Hu; cbn [a_base a_off] in Hu.
  unfold uE. rewrite <- Hu, !Z_to_bv_bv_unsigned. exact Hr.
Qed.

Lemma covers_sound : forall E b off n a len, covers b off n a len = true -> flat E a (elenZ E len) ->
  exists L, elenZ E len = L /\ a_base a = b /\ a_off a <= off /\ off + n <= a_off a + L /\ 0 <= n.
Proof.
  intros E b off n a len H Hf. unfold covers in H. destruct len as [L|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate.
  repeat (apply andb_prop in H as [H ?]). apply expr_eqb_eq in H.
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  exists L. unfold elenZ. cbn [edenot]. destruct Hf as (_ & _ & F3 & _). unfold elenZ in F3. cbn [edenot] in F3.
  rewrite u64_lit by (pose proof (u64_range (Z_to_bv 64 L)); split; [|assumption]; destruct (Z_lt_dec L 0); [|lia];
                      exfalso; lia).
  repeat split; assumption || lia.
Qed.

Lemma hc_zero : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> chk_zero (kn cs) b off n = true ->
  0 <= uE E b + off /\ uE E b + off + n <= 2 ^ 64
  /\ forall i, 0 <= i < n -> FULL (Z_to_bv 64 (uE E b + off + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E cs R FULL model b off n HC H. unfold chk_zero in H. apply existsb_exists in H as (K & Hin & Hc).
  destruct K as [| a len | | | | | | | |]; try discriminate.
  destruct (hb_zero_k SEGS A LIMIT SINV argH FS0 E cs R FULL model a len HC Hin) as [Hf Hz].
  destruct (covers_sound E b off n a len Hc Hf) as (L & HL & Hb & H1 & H2 & H3).
  destruct Hf as (F1 & F2 & F3 & F4). unfold estart in *. rewrite Hb in *. rewrite HL in *. unfold uE.
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E b) + a_off a + (off - a_off a + i)) by ring.
  apply Hz. lia.
Qed.

Lemma wleb_zero : forall w, (w <= 8)%nat -> word_to_le_bytes w (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) w.
Proof.
  intros w Hw. do 9 (destruct w as [|w]; [vm_compute; repeat f_equal; apply bv_eq; reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma hc_zero_cell : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> chk_zero (kn cs) b off n = true ->
  forall a (w : nat), (w <= 8)%nat -> uE E b + off <= a -> a + Z.of_nat w <= uE E b + off + n ->
    rdn SEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 0)).
Proof.
  intros E cs R FULL model b off n HC H a w Hw Ha1 Ha2.
  destruct (hc_zero E cs R FULL model b off n HC H) as (Z1 & Z2 & Hz).
  rewrite (wleb_zero w Hw). destruct w as [|w']; [reflexivity|]. apply rdn_const.
  - rewrite u64_lit by lia. lia.
  - intros x Hx. rewrite u64_lit in Hx by lia.
    replace x with (Z_to_bv 64 (uE E b + off + (bv_unsigned x - (uE E b + off)))).
    + apply Hz. lia.
    + replace (uE E b + off + (bv_unsigned x - (uE E b + off))) with (bv_unsigned x) by ring. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hc_wr : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> chk_wr (kn cs) b off n = true ->
  forall d (m : nat), 0 <= d -> d + Z.of_nat m <= n -> store_ok SEGS FULL (Z_to_bv 64 (uE E b + off + d)) m = true.
Proof.
  intros E cs R FULL model b off n HC H d m Hd Hm. unfold chk_wr in H. apply existsb_exists in H as (K & Hin & Hc).
  destruct K as [| | | | | | a len | | |]; try discriminate.
  pose proof (hb_kn SEGS A LIMIT SINV argH FS0 E cs R FULL model _ HC Hin) as HK. cbn [kentry_ok] in HK. destruct HK as [Hf HW].
  destruct (covers_sound E b off n a len Hc Hf) as (L & HL & Hb & H1 & H2 & H3).
  unfold estart in *. rewrite Hb in *. rewrite HL in *.
  pose proof (HW (off - a_off a + d) m ltac:(lia) ltac:(lia)) as Hs.
  replace (bv_unsigned (edenot E b) + a_off a + (off - a_off a + d)) with (uE E b + off + d) in Hs by (unfold uE; ring).
  exact (proj1 (hb_mr_store_ok SEGS A argH SEGS_in_hull HULL_ok argH_high E cs model FULL _ m Hs)).
Qed.

Lemma hc_img : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> chk_img (kn cs) a w v = true ->
  rdn SEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof.
  intros E cs R FULL model a w v HC H. unfold chk_img in H.
  destruct (kfind_img (kn cs) a) as [[lo hi]|] eqn:Hk; [|discriminate].
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  destruct (rdn SEGS (fun _ => None) (Z_to_bv 64 a) w) as [bs|] eqn:Hr; [|discriminate].
  match goal with X : bytes_eqb _ _ = true |- _ => apply bytes_eqb_eq in X; subst bs end.
  rewrite <- Hr. apply rdn_ext.
  - rewrite u64_lit by lia. lia.
  - intros x Hx. rewrite u64_lit in Hx by lia.
    cbn beta. replace x with (Z_to_bv 64 (bv_unsigned x)) by apply Z_to_bv_bv_unsigned.
    apply (hb_img_at SEGS A LIMIT SINV argH FS0 HULL_ok argH_high E cs R FULL model a lo hi HC Hk); [lia|].
    unfold in_hull. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* [comment removed for export] *)
Definition chk_sub (k : list kentry) (a : Z) (w : nat) (v : Z) : bool :=
  existsb (fun K => match K with
                    | KWord (SA (ELit 0) a0) w0 (ELit v0) =>
                        (* [comment removed for export] *)
                        if (Z.leb 0 a0 && Z.leb a0 a && Z.leb (a + Z.of_nat w) (a0 + Z.of_nat w0) && Z.ltb 0 (Z.of_nat w))%bool
                        then bytes_eqb (firstn w (skipn (Z.to_nat (a - a0)) (word_to_le_bytes w0 (Z_to_bv 64 v0)))) (word_to_le_bytes w (Z_to_bv 64 v))
                        else false
                    | _ => false
                    end) k.

Lemma hc_sub : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> chk_sub (kn cs) a w v = true ->
  rdn SEGS FULL (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Proof.
  intros E cs R FULL model a w v HC H. unfold chk_sub in H. apply existsb_exists in H as (K & Hin & Hc).
  destruct K as [[b a0] w0 v0| | | | | | | | |]; try discriminate.
  destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
  destruct v0 as [v0| | | | | | |]; try discriminate.
  match type of Hc with (if ?c then _ else _) = true => destruct c eqn:Hg; [|discriminate] end.
  apply bytes_eqb_eq in Hc. rename Hc into Hb. rename Hg into Hc.
  repeat (apply andb_prop in Hc as [Hc ?]).
  repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
  destruct (hb_word SEGS A LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E cs R FULL model _ w0 _ HC Hin) as (Hw & Hf & Hr & _).
  pose proof (flat_u E _ _ Hf) as Hu. unfold estart in Hu; cbn [a_base a_off edenot] in Hu.
  destruct Hf as (F1 & F2 & F3 & F4). unfold estart in F1, F2, F4; cbn [a_base a_off edenot] in F1, F2, F4.
  rewrite u64_lit in Hu, F1, F2, F4 by lia. rewrite Z.add_0_l in Hu, F1, F2, F4.
  cbn [edenot] in Hr.
  pose proof (rdn_slice SEGS FULL w0 _ _ (Z.to_nat (a - a0)) w Hr ltac:(lia)) as Hs.
  rewrite Hb in Hs. rewrite <- Hs. f_equal.
  apply bv_eq. rewrite u64_lit by lia.
  unfold nat_to_word. rewrite bv_add_unsigned, Hu. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.mod_small (Z.of_nat (Z.to_nat (a - a0)))) by lia. rewrite Z.mod_small by lia. lia.
Qed.
End Cells.

End HandoffCellsK.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK.
Module HandoffLazyK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma hl_iv_subtract_apart : forall (a sz : word) lo hi q,
  bv_unsigned a + bv_unsigned sz <= 2 ^ 64 ->
  In q (iv_subtract a sz lo hi) ->
  bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_subtract in Hin.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. left. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite (u64_lit (Z.max (bv_unsigned a) hi)) by lia. right. lia.
Qed.

Lemma hl_maps_subtract_apart : forall l lo hi q,
  (forall p, In p l -> bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) ->
  In q (maps_subtract l lo hi) ->
  bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hl Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (hl_iv_subtract_apart a sz lo hi q (Hl (a, sz) (or_introl eq_refl)) Hin).
  - exact (IH lo hi q (fun p Hp => Hl p (or_intror Hp)) Hin).
Qed.

(* [comment removed for export] *)
Lemma hl_replay_sub : forall E h1 bS nS h2,
  (forall b n, In (HCons b n) (h1 ++ HSub bS nS :: h2) -> uE E b + uE E n <= 2 ^ 64 /\ 0 < uE E n) ->
  (forall b n, In (HCons b n) h1 -> uE E b + uE E n <= uE E bS \/ uE E bS + uE E nS <= uE E b) ->
  forall q, In q (hreplay E (h1 ++ HSub bS nS :: h2)) ->
    bv_unsigned (fst q) + bv_unsigned (snd q) <= uE E bS \/ uE E bS + uE E nS <= bv_unsigned (fst q).
Proof.
  intros E h1 bS nS h2. induction h1 as [|hop h1 IH]; intros Hwf Hap q Hin.
  - cbn [app hreplay] in Hin.
    apply (hl_maps_subtract_apart (hreplay E h2) _ _ q); [|exact Hin].
    intros p Hp. destruct (hl_replay E h2 (fun b n H => Hwf b n (or_intror H)) p Hp) as (_ & P2 & _). exact P2.
  - assert (IH' := IH (fun b n H => Hwf b n (or_intror H)) (fun b n H => Hap b n (or_intror H))).
    destruct hop as [b n|b n]; cbn [app hreplay] in Hin.
    + destruct Hin as [<-|Hin]; [|exact (IH' q Hin)]. cbn [fst snd]. exact (Hap b n (or_introl eq_refl)).
    + assert (WF : forall p, In p (hreplay E (h1 ++ HSub bS nS :: h2)) ->
                     0 < bv_unsigned (snd p) /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64).
      { intros p Hp. destruct (hl_replay E _ (fun b' n' H => Hwf b' n' (or_intror H)) p Hp) as (P1 & P2 & _). auto. }
      destruct (hl_maps_subtract (hreplay E (h1 ++ HSub bS nS :: h2)) _ _ q (fun p Hp => let '(conj P1 P2) := WF p Hp in conj P2 P1) Hin)
        as (_ & p & Hp & Q2 & Q3).
      destruct (IH' p Hp) as [X|X]; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Lemma hl_page_piece : forall (w : word) lazy, page_in_ranges (page_base w) lazy = true ->
  exists q, In q lazy /\ bv_unsigned (fst q) <= bv_unsigned (page_base w) /\ bv_unsigned (page_base w) + 4096 <= bv_unsigned (fst q) + bv_unsigned (snd q).
Proof.
  intros w lazy H. unfold page_in_ranges in H. apply existsb_exists in H as (q & Hq & Hb). apply andb_prop in Hb as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. exists q. unfold page_size in B2. auto.
Qed.

End HandoffLazyK.
Module HandoffRolesK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BackingAlgebra. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AxSymRun3K AsanPlanSoundK. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BackingAlgebra OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymRun3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffLedgerK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition AM_DUMMY : amap := {| am_base := ELit 0; am_len := ELit 0; am_kind := KRW |}.
Definition role (cs : acs) (i : nat) : amap := nth i (rev (a_maps cs)) AM_DUMMY.
Definition rbase (E : env) (cs : acs) (i : nat) : Z := uE E (am_base (role cs i)).
Definition rlen (E : env) (cs : acs) (i : nat) : Z := uE E (am_len (role cs i)).

Lemma role_in : forall cs i, (i < length (a_maps cs))%nat -> In (role cs i) (a_maps cs).
Proof. intros cs i Hi. unfold role. apply in_rev. apply nth_In. rewrite length_rev. exact Hi. Qed.

Lemma seps_rev_nth_apart : forall l, seps l -> (forall q, In q l -> 0 < bv_unsigned (snd q)) ->
  forall d i j, (i < length l)%nat -> (j < length l)%nat -> i <> j ->
    iv_disjoint (nth i (rev l) d) (nth j (rev l) d).
Proof.
  intros l Hs Hpos d i j Hi Hj Hne.
  pose proof (hl_seps_nodup l Hs Hpos) as ND. apply NoDup_rev in ND.
  assert (Hq : nth i (rev l) d <> nth j (rev l) d).
  { intros Heq. apply Hne. apply (proj1 (NoDup_nth (rev l) d) ND i j); rewrite ?length_rev; assumption. }
  pose proof (hl_seps_apart l Hs (nth i (rev l) d) (nth j (rev l) d)) as Hap.
  unfold iv_disjoint. unfold BackingAlgebra.B, BackingAlgebra.S in Hap.
  apply Hap; [apply in_rev; apply nth_In; rewrite length_rev; assumption | apply in_rev; apply nth_In; rewrite length_rev; assumption | exact Hq].
Qed.

Section Roles.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).

Lemma role_den : forall E cs R FULL model i, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  nth i (rev (vm_maps (m_vmmaps model))) (amap_den E AM_DUMMY) = amap_den E (role cs i).
Proof.
  intros E cs R FULL model i HC Hnf. rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf).
  rewrite <- map_rev. unfold role. apply map_nth.
Qed.

Lemma role_geo : forall E cs R FULL model i, CSOK E cs R FULL model -> no_fog (a_maps cs) = true -> (i < length (a_maps cs))%nat ->
  0 < rlen E cs i /\ rbase E cs i mod 4096 = 0 /\ rlen E cs i mod 4096 = 0
  /\ (rbase E cs i + rlen E cs i <= img_lo A \/ img_hi A <= rbase E cs i)
  /\ rbase E cs i + rlen E cs i <= uE E e_sp0 - 8388608
  /\ 0 <= rbase E cs i /\ rbase E cs i + rlen E cs i <= 2 ^ 64.
Proof.
  intros E cs R FULL model i HC Hnf Hi.
  assert (Hin : In (amap_den E (role cs i)) (vm_maps (m_vmmaps model))).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply in_map. apply role_in. exact Hi. }
  pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) _ Hin) as (P1 & P2 & P3 & P4 & P5).
  pose proof (utop_bounds E) as UT.
  destruct (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W & _). pose proof (W _ Hin) as Wq.
  unfold BackingAlgebra.iv_wf, BackingAlgebra.B, BackingAlgebra.S in Wq.
  unfold amap_den in *. cbn [fst snd] in *. unfold rbase, rlen, uE in *.
  pose proof (u64_range (edenot E (am_base (role cs i)))). repeat split; try assumption; lia.
Qed.

Lemma role_apart : forall E cs R FULL model i j, CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  (i < length (a_maps cs))%nat -> (j < length (a_maps cs))%nat -> i <> j ->
  rbase E cs i + rlen E cs i <= rbase E cs j \/ rbase E cs j + rlen E cs j <= rbase E cs i.
Proof.
  intros E cs R FULL model i j HC Hnf Hi Hj Hne.
  assert (Hlen : length (vm_maps (m_vmmaps model)) = length (a_maps cs)).
  { rewrite (hb_maps SEGS A LIMIT SINV argH FS0 E cs R FULL model HC Hnf). apply length_map. }
  pose proof (seps_rev_nth_apart _ (co_seps _ _ _ _ _ _ _ _ _ _ _ HC)
                (fun q Hq => proj1 (hl_maps_pos SEGS A LIMIT SINV argH FS0 E cs R FULL model q HC Hq))
                (amap_den E AM_DUMMY) i j ltac:(rewrite Hlen; exact Hi) ltac:(rewrite Hlen; exact Hj) Hne) as D.
  rewrite !(role_den E cs R FULL model _ HC Hnf) in D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
  unfold rbase, rlen, uE. exact D.
Qed.
End Roles.

Lemma role_lit : forall E cs i L, am_len (role cs i) = ELit L -> 0 <= L < 2 ^ 64 -> rlen E cs i = L.
Proof. intros E cs i L H HL. unfold rlen, uE. rewrite H. cbn [edenot]. apply u64_lit. exact HL. Qed.

End HandoffRolesK.
