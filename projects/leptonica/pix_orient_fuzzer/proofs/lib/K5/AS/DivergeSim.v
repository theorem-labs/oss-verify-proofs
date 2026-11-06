(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_DivergeSim () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem3Run>is_prefix_reflC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilC4ELinuxProcessSemantics?LinuxProcessSem3Run?is_prefix_transC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic9False_indC47Corelib4Init9Datatypes8list_indK47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesK47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01C4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateDmaterialize_accessesK47Corelib4Init9Datatypes6option02I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessc69OSSVerify5KrLib2K52AS:DivergeSimNmaterialize_model_accesses_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimKmi_account_step_of_accessesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunKmi_account_step_model_frameC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State=procst_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC69OSSVerify5KrLib2K52AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr03C4ELinuxProcessSemantics5Riscv3Sem5is_x0C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setc69OSSVerify5KrLib2K52AS:DivergeSim8v_addi_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec9b_addsextC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01c69OSSVerify5KrLib2K52AS:DivergeSimGself_jump_step_accessesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimImi_account_step_no_accessC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib2K52AS:DivergeSim;silent_loopC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01K47Corelib4Init5Logic2ex01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K4ELinuxProcessSemantics?LinuxProcessSem5State5event04K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02c69OSSVerify5KrLib2K52AS:DivergeSimAsilent_loop_sstepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_indc69OSSVerify5KrLib2K52AS:DivergeSim@silent_loop_starC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C4ELinuxProcessSemantics?LinuxProcessSem3Run=reaches_errorC47Corelib4Init5Logic3notc69OSSVerify5KrLib2K52AS:DivergeSimDsilent_loop_no_errorC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunEno_error_no_unmodeledC4ELinuxProcessSemantics?LinuxProcessSem3Run9obs_tracec69OSSVerify5KrLib2K52AS:DivergeSimDsilent_loop_star_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimAis_prefix_nil_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_nilI4ELinuxProcessSemantics?LinuxProcessSem3Run@all_traces_error00K4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep01C4ELinuxProcessSemantics?LinuxProcessSem3RunDall_traces_error_indk69OSSVerify5KrLib2K52AS:DivergeSim7to_spin01C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2K52AS:DivergeSim7to_spin00C1?~~~~~~~~~~~~~~~k69OSSVerify5KrLib2K52AS:DivergeSim7to_spin02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunGmi_account_step_no_lazyc69OSSVerify5KrLib2K52AS:DivergeSimAts_spin_no_accessC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSim8spinningC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimFmi_account_step_haltedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimDspinning_silent_loopC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimCsilent_loop_obs_iffC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimHsilent_loop_no_unmodeledC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimJsilent_loop_not_all_errorsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimAobs_trace_of_starC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rc69OSSVerify5KrLib2K52AS:DivergeSim=spin_star_nilC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSim<is_self_jumpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbK4ELinuxProcessSemantics5Riscv5Instr5instr01K4ELinuxProcessSemantics5Riscv5Instr5instr02C47Corelib4Init9Datatypes9andb_propC56Stdlib6ZArith6BinInt1Z6eqb_eqc69OSSVerify5KrLib2K52AS:DivergeSimAts_spin_of_step_jC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5instr0;K4ELinuxProcessSemantics5Riscv5Instr5instr0<K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5instr0>K4ELinuxProcessSemantics5Riscv5Instr5instr0?K4ELinuxProcessSemantics5Riscv5Instr5instr0BK4ELinuxProcessSemantics5Riscv5Instr5instr0CK4ELinuxProcessSemantics5Riscv5Instr5instr0DK4ELinuxProcessSemantics5Riscv5Instr5instr0EK4ELinuxProcessSemantics5Riscv5Instr5instr0FK4ELinuxProcessSemantics5Riscv5Instr5instr0GK4ELinuxProcessSemantics5Riscv5Instr5instr0HK4ELinuxProcessSemantics5Riscv5Instr5instr0IK4ELinuxProcessSemantics5Riscv5Instr5instr0JK4ELinuxProcessSemantics5Riscv5Instr5instr0KK4ELinuxProcessSemantics5Riscv5Instr5instr0LK4ELinuxProcessSemantics5Riscv5Instr5instr0MK4ELinuxProcessSemantics5Riscv5Instr5instr0NK4ELinuxProcessSemantics5Riscv5Instr5instr0OK4ELinuxProcessSemantics5Riscv5Instr5instr0PK4ELinuxProcessSemantics5Riscv5Instr5instr0QK4ELinuxProcessSemantics5Riscv5Instr5instr0RK4ELinuxProcessSemantics5Riscv5Instr5instr0SI4ELinuxProcessSemantics5Riscv5Instr;branch_cond00I4ELinuxProcessSemantics5Riscv5Instr5msize00I4ELinuxProcessSemantics5Riscv5Instr5aluop00K4ELinuxProcessSemantics5Riscv5Instr5instr0@K4ELinuxProcessSemantics5Riscv5Instr5instr0AI4ELinuxProcessSemantics5Riscv5Instr5mulop00I4ELinuxProcessSemantics5Riscv5Instr6awidth00I4ELinuxProcessSemantics5Riscv5Instr5amoop00I4ELinuxProcessSemantics5Riscv5Instr5csrop00I4ELinuxProcessSemantics5Riscv5Instr4ffmt00I4ELinuxProcessSemantics5Riscv5Instr5fmaop00I4ELinuxProcessSemantics5Riscv5Instr6fariop00I4ELinuxProcessSemantics5Riscv5Instr6fsgnop00I4ELinuxProcessSemantics5Riscv5Instr9fminmaxop00I4ELinuxProcessSemantics5Riscv5Instr6fcmpop00I4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty00I4ELinuxProcessSemantics5Riscv5Instr6fmvdir00c69OSSVerify5KrLib2K52AS:DivergeSim6spin_cC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02c69OSSVerify5KrLib2K52AS:DivergeSimDis_self_jump_to_spinC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indK47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib2K52AS:DivergeSim9star_caseC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSimBis_prefix_app_monoC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K4ELinuxProcessSemantics?LinuxProcessSem3Run4star02C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo01C4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC45stdpp9bitvector;definitions9bv_eq_decI4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c79OSSVerify5KrLib2K52AS:DivergeSim=SelfJumpImage9spin_segsC1?~~~~~~~~~~~~~~~C35stdpp9decidable;bool_eq_decc79OSSVerify5KrLib2K52AS:DivergeSim=SelfJumpImage=j_dot_decodesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC47Corelib4Init5Logic3iffc79OSSVerify5KrLib2K52AS:DivergeSim=SelfJumpImage@spin_img_to_spinC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:DivergeSim<spin_obs_iffC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configK4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00c79OSSVerify5KrLib2K52AS:DivergeSim=SelfJumpImage8spin_imgC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsc69OSSVerify5KrLib2K52AS:DivergeSimAspin_no_error_runC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run=bh_all_errorsc69OSSVerify5KrLib2K52AS:DivergeSimCspin_not_all_errorsC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw01c69OSSVerify5KrLib2K52AS:DivergeSim>spin_c_to_spinC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;mkProcInputK4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream01C4ELinuxProcessSemantics?LinuxProcessSem5State:net_silentC4ELinuxProcessSemantics?LinuxProcessSem5State>default_nofileC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<hwcap_rv64gcK4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_nil_inv {A} : forall (tr : list A),
  is_prefix tr [] -> tr = [].
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "p'0h02trh11Ah21ai001ai011lp;1p;3p;2p10000p4p70R0p1000`p4p710R1p8P0p10017p4p710R2p8P0p1001Sp4p710R3p8P0p1001op4p710R4p8P0p1002Mp4p7210R5p8P0p1002jp4p710R0p8p200R6g003HR7p4p710R8p8p1004>p4p70R9P1p8P9P2p8P9P3p8P9P8p8P9p1004lp4p710p8P9p1005Ip4p710p8P9P6p8P9p1006Dp4p710p8P9P4p8P9P5p8P9p1007>p4p710p8P9P0p8P9p1008:p4p710p8p1008Wp4p7210R9P1p8P9P2p8P9P3p8P9P4p8P9P5p8P9P0p8P9p1009Cp4p710p8p100:Jp4p70R9P1p8P9P2p8P9P3p8P9P4p8P9P5p8P9P0p8g00;@R0j10Tg00;`j11TP7j32Tg00<@j33Tg00<Zj26Tg00=4j34Tg00=Tj25Tf0R7#0P0f1R0f2R9%19R5727f3R4#0%14730[P7%10R3=203%09/65Uf4#0f5R5A4507%1532f6R5#0A4590%1533/57UW0X24P0P7O2n10110100020020100101W0X16o"). Qed.

Lemma is_prefix_app_mono {A} : forall (e a b : list A),
  is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "h01ah11bh21eh31Hh41Ah53IHeh62a0p;1p;3p;2p;4p;5p200R0g003HR1p4p710p8P0g00>3R2p4p710p8P0g008:R3p4p710p8p1004>p4p70P0p8g00;@j12TP1j31TP3j30Tg00;`j13Tg00<@j38Tg00<Zj27Tg00>Uj46Tg00=4j34TP2j55Tf0R2#2f1R3%23R1f2R4#2R5f3R6#2R7f4R8?132f5R9A0964A096331[]1]0W2A1632R:P2W3X15X01%38R;=084A08;3518\:^15^01e%28R1A1932f6R:A0:64A0:6331[]1^07%29R7A1:32R:f7R;?899A0;84A0;8351;17;9P6P4P3P2O3C6W3W1X61A4;98R9=0;4A0;9351;\:^17^01eW5X25X03P2D5W2X40o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "p'0h06m_timei006m_timeh12fdh22fsh32ioh44lazyh53limh61mi011mh76m_fsysi026m_fsysh84m_ioi034m_ioh95m_limi045m_limh:6m_proci056m_proch;4m_vmi064m_vmh<4mapsh=<materializedh>4proci074m_fdi085pagesi091vi0:9vmst_lazyi0;9vmst_mapsi0<Avmst_materializedi0=1xp;1p;2p;3p;7p;5g00?0R0j1DTg00?Rj10Tg00@7j1<Tg00@Uj1;Tg00A8j26Tg00;`j1BTg00AXj24Tg00Baj22Tg00<@j31Tg00CCj73Tg00;@j15Tg00D9j37Tg00<Zj2:Tg00E1j39Tg00Eoj18Tg00Fgj1CTg00Ggj1ATg00Hej1?Tg00I\j1>Tg00JSj5=Tg00KVj1@Tg00L8R1P1%D1R2f0R3g00Ln#0#0#0#0#0#0#<#;R4g00MS'6#BR5'4121331P3g00N2g00NjR6P6g00ObR6g00PZR7g00QRR8g00RLR9g00SER:f7R;f5R<f4R=f3R>f2R?f1R@P3F3RA/45121A512]0]9]:]7]8P3g00T?1644#5%54R4f<f6RA=7;<P=P>P?P@P3F3RB,21RC,:2A9A<B,21=12CRDePDeP0P4P2%8B%CB%AB%?B#>P5D=f=f8?7;AP<P=P>P?P@F3R;#8?93;,21%@1n10110=00021010800=12Ce14B5=12CeX0:X59X>8X27X36W=W4W<P?P@P3O3n0110900013110;10:10<W;W1PAP<P=P>P?P@P3O7n01101000171107106103102105104100W6o"). Qed.

(* [comment removed for export] *)
Lemma mi_account_step_of_accesses : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  mi_account_step segs ms model =
    match materialize_model_accesses model ranges with
    | Some model' => MachineOk (ms', model')
    | None => MachineFault
    end.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "p'0h05Hsteph11mh25modelh32msh43ms'h56rangesh64segsi006model'i016reporti021xp;1p;2p;3p;6p;4g00;@j16Tg009Cj1ATg00U6R0j14Tg00V>j25Tg00WCj37Tg00XJj20Tg00<@j32Tg00A8j2;Tg00YRj2:Tg00AXj21Tg00ZYj28Tg00[]j19Tg00\ej1@Tg00<Zj2?Tg002jj6>Tg00]mj3<Tg00^ij4=Tg00_IR1g00L8R2f1R3f0R4C=p=3g00`P#6g00aO#6%A1R5#4R6f4R7f3R8'5A7134,0532P6f2R9=713,051;12R:#4R;P0P5P;P4g00?0R5P2P;f5R01:14'11813/34,0:%9:R<n10110200021010000P<%@:n1011020003101010000P5P2P;11791374,0:P<n1011020002101000032X16P5P2P;11831384,0:P<n10110200021010000R<,?;1507P4E>A<078=2;<eW0W5X41X22X31W6o"). Qed.

(* [comment removed for export] *)
Lemma mi_account_step_no_access : forall segs ms model ms',
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "p'0h05Hsteph11mh25modelh32msh43ms'h51oh64segsi006model'i011xp;1p;2p;3p;6p;4g00;@j1FTg009Cj1ETg00U6j14Tg00V>j2;Tg00;`j18Tg00WCj3ATg00XJj21Tg00<@j33Tg00A8j25Tg00AXj26Tg00[]j1:Tg00?0R0j19Tg00Baj2DTg00<Zj2CTg00?Rj10Tg00@7j1@Tg00@Uj1?Tg00bTj1>Tg002jj67Tg00]mj3=Tg00chj6BTg00^ij4<Tg00_IR1g00L8R2f1R3f0R4C<p=2g00`P#F%E1R5#4f3R6f2R7';g00aO#8R89A14,15331512R5#4R9P0P2P916781274,15%:5R:n101101000210100001276,15R;9394X19%92R<1D27P0P2P9P41264,15P:n10110100021010000=39;X5<1237,15,C9g00Ln#0#0#0#0#0#0#@#?g00MS'5#8,67%>7E7f4R9?=67P9P6P7P3P8P4EBE7W0X41X22X31W6o"). Qed.

(* [comment removed for export] *)
Lemma mi_account_step_halted : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  m_halted model' = m_halted model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "h01Hh14Hacch25Hproch32_Hh43_H0h53_H1h63_H2h73_H3h83_H4h91ah:5modelh;6model'h<2msh=3ms'h>1ph?4segsp;1p;2p;3p;4p;6g00;@j1CTg00A8j2DTg00U6j1OTg00]mj3HTg00^ij4RTg00XJj2QTg00<@j30Tg00e9j6NTg00fAj1=Tg00Hej16Tg00?Rj1<Tg00@7j1FTg00@Uj1ETg00Eoj13Tg00g4j15Tg00ggj11Tg00?0j1PTg00h\j12Tg00iSj1:Tg00jHj1@Tg00<Zj2GTg002jj6LTg00kDj1?Tg00l8R0j2>Tg00ObR1f1R2#5f0R330p=9g00PZR4%12;03p=8g00QRR5f3R6#:f2R7#:30g00RLR8%?2%?330'>p=41>23,>7p=;A0672/>3p=7A0472/>3p=B%539012p=M%139042p=K%:2=053p=J%?2%?3508p=AA0523p=Ig00`P#Cg00_IR8g00L8R41D84R1#Of4R9?H67P8P4P2P3CR,Q130f5R1P9P6P7P2P3ENg00N2R:%=2%=6g00T?R;%62%66g00Ln#<#<#<#<#<#<#F#ER</D<#CR=%32%36%56,92%16,82P2P6P2P6C43;C7C7C7P0%=7%=9R>50:P;%67%69P=%37%39%59,97%19,87P7P9P7P9C43;C7C7%P<R<%26%2130P3f6R6#=90:>P;%61f7R>#6P=%31%3>%5>,91%1>,81P1P>P1P>C43;C7C7P0%66f8R1#6R:50;P=%36%31%51,96%11,86P6P1P6P1C43;C7%2>f9R>#250<P3f:R1#690;:P=%3>f;R:#3%5:,9>%1:,8>P>P:P>P:C43;C7P0%31f<R>#3R;50=%5>,91%1>,81P1P>P1P>C43;%2:f=R:#250<P3f>R>#390=;f?R;#5,9:%1;,8:P:P;P:P;C43;P0f@R:#5R=,9>%1>%1:P>P:P>P:C43B%2;fAR;#250<P3fBR:,M=%1;fCR=#1P;P=P;P=C43BP0fDR;#1R>,8:P:P;P:P;C4%2=fER=#250<P3fFR;,K>P=fGR>P=P>C4P0fHR0#:R=,J;1A;0%2>fIR>#250<P3fJR0#:R;,I=fK,A>P5fLR>#:R=%@3fM#:#@50<X>5%@=,G<P;P2EL%20%2>50<eW8W2P2P3O2n2001000000120000000W0W7P2P3O2n2001000000120000000W0W6P2P3O2n2001000000121000000W0W5P2P3O2n2001000000121000000W0W4P2P3O2n2001000000121000000W0W3P2P3O2n2001000000121000000b9W1X;4X=8W:W<W?o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_0 : forall a : word, v_addi a 0 = a.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "h01ah11zp;1p;2p;3p;6g00?Rj10Tg00@7j1:Tg00@Uj13Tg00lSj22Tg00m=j29Tg00<@j31Tg00mcj28Tg00nUj24Tg00o2j15Tg002jj66Tg00oSj27Tg00Ln#0#0#0#0#0#0#:R0#3R1g010MR2f0R3,20R41903f1511X121803g010kR0,44%54E61730=113eW0o"). Qed.

(* [comment removed for export] *)
Lemma self_jump_step_accesses : forall segs ms w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "p'0h06Hfetchh14Hsvch21bh3>ms_svc_pendingi00>ms_svc_pendingh41oh57Hdecodeh66Hecallh74Himmh83Hx0h93immh:2msh;7ms_fcsri017ms_fcsrh<8ms_fregsi028ms_fregsh=6ms_memi036ms_memh>9ms_pc_vali049ms_pc_valh?7ms_regsi057ms_regsh@7ms_resvi067ms_resvhA6ms_romi076ms_romhB2rdhC4segshD2szhE1wi081whF1zi091ci0:6c_fcsri0;7c_fregsi0<4c_pci0=6c_regsi0>6c_resvi0?1ii0@3iszi0A1mi0B2m'i0C1pi0D6reporti0E3st'i0F1xp;1p;3p;2p;4p;8p;5p;7p;6g00;@j1qTg00?Rj1>Tg00@7j1ETg00@Uj1DTg011Ij1NTg00?0R0j1FTg011nj1MTg00KVj1cTg00<@j30Tg0134j1<Tg0141j2BTg00Baj25Tg0153j1PTg00A8R1j2YTg0163j1KTg016dj2XTg00^ij4LTg017Pj1TTg0188j2STg009Cj1UTg00U6R2j1eTg018`j3QTg019lj16Tg01:jj3bTg01;oj3aTg01=5j3`Tg00;`j1_Tg00[]j1^Tg00\ej1]Tg01>:j17Tg01?9j19Tg01@9j1;Tg01A:j1\Tg01AXj3[Tg01B;j2ZTg01C9j18Tg01D8j1:Tg01E7j1?Tg01F5j83Tg00m=j2ITg01G<j51Tg01Gej3OTg01HLj3JTg00ZYj2ATg01IWj1pTg01J@j1oTg01Jjj1nTg01KQj1mTg01L:j1jTg00YRj2=Tg01Lcj1VTg01M\j3GTg01NGj3CTg01Nlj5RTg008Wj2iTg00oSj2HTg00<Zj2gTg002jj7fj6@Tg01O\j1hTg01PZj3kTg00V>j2lTg00WCj3WTg00XJj2dTf2R3g00_IR4f1R5f0R63W'dp=2f4R7g01QWR8f3R9P3P5CL;W6p=4g00`P#qg00Ln#>R:#>#>R;#>#>R<#E#DR=%N:R:#ER>#D%>:#N#ER:#Dg010MR?%><#ER<#DR@#FRA%M7%c@RB30%F=RCf6RDf5RE#<'B15=730g01R@RF%PEg01R`RG30g01S@RH/Y?RI#FRJ%KDPHP?1XE7P9CL,5I30%TDg01SlRK50F1S:Dg010kRL50?PCf9RM,5=%U4RN#eROP0P=POP6f=RPf<RQ;Q6RRP0P=POf;RS#6RT%<SRU5bQPRP0P=POAaQTUPRP2P4POA`QTUg00aO#_RU92N6%^NRR%]NRVn10110F00031010E0000n10110F00021010800n10110F00021010800n10110F00021010800A2NSURW30X4CPFPGPFPOP6%7SRG%9SRX%;SRY%N;#\g01TL5[>,ZS,5@%8SRZ%:SR[PT%?SG3=2NUP0PIPOf:R\#KP1PHP?POP6P2%E;#D#F\@R;,Y8R]#UR^POf?1I<6R_f>R`#7%9`%;`%:`%8`D17O5%6`3JP1P8P;PO1A]6Ra%p5Rb%o5Rc%n5RdPB%m5Re%j5RfP6fA#?G31=]3Rg52Nn200110F00012010910BPRPVn10110F00031010D0000n200110C00012010?10@RhPFPO%V\PRPVn0100000020000Rin10110F00021010C00n0100000020000=0OWX2FPJPHP?f8Rjf7Rk'XRlPDCL,5IP0PIPOP6PhPin10110F00021010C00=0OWX4JPFPKP1P8P;POP]P;PFP8P6PGPXAG:<j9C<YRKP[PZD1P>P@PM1I<k9C<YPGDRPXPKP[PZD1n0100000020000PTPUD4,A]P81i>@RKP5P7n0110900015010=10;10<10:10>RJP8PKP5P9n0110900015010=10;10<10:10>RiP8P@P5P3n0110900015010=10;10<10:10>RhPBP8PAP5P6n0110900015010=10;10<10:10>RmP8P=P5P5n0110900015010=10;10<10:10>RnP6%?PRoG3RpP]P;PFP8P3%7PRq%9PRr%;PRsAG:<\5C<Rt%:PRu%8PRvD1P>P@PS1I<M9C<sPqDRPrPtPuPvD1n0100000020000%6PRtPUD4,=]52Nn200110F00012110910B=0OWX2FP@%;\R>1S:kRw'HP1P8P;POP]P;PGPXP6P[PZD1PTPUD4,A]P]P;PqPrP3PuPvD1PtPUD4,=]92Npn200110F00012010910B=0OWX2@RxP?PLP1P8P;POP]P;PGPX1HY6P[PZD1PTPUD4,A]P]P;PqPr1Hs3PuPvD1PtPUD4,=]92Npn200110F00012010910B=0OWXF?P@P>PxP4%M6=0AB%<5,BP15=S50CP1P8P;POP]P;%73%93%;3%:3%83D1%63PUD4,A]PJPiPhPBPmPnP6%?7G3P]P;%77%97%;7%:7%87D1%67PUD4,=]52Nn200110F00012010910BA2N3U50O]0]1P\PkPDPEP7P9P3P5P6G3#M=0ABfLRxPjPkPDPEP7P9P3P5G3#<'BfJ,5=50CPAPBfNP\PMPjP6PDPEP7P9G3#<'B15=x50CP1P8P;POP]P;PSP\PMP5PkPDPEP7G3Rx#7%9x%;x%:x%8xD1%6xPUD4,A]PJPiPhPBPmPnP6PPPQPSP9PMPjPkPDG3RP#?G3P]P;%7P%9P%;P%:P%8PD1%6PPUD4,=]52Nn200110F00012110910BA2NxU50O]0X3AfMPMPjPkPBPEP7P9P3G3#<'BfK,5=50CP\PMPjPBPDPEP7P9G3=2NU,gOW0PDP5P6FfW0W1XA;X=;X;=X@AX3AX>@X<KX?KPkPDPEP7P9P3P5P6O8n0110A010181105102104100106101103107PEP7O21H>L%h>E@PwP6E@AG:<k9C<>RwAk>:kE@P1P8P;POP]P;%7\Rk%9\RLPw%:\Rw%8\RED1%6\RKPUD4,A]PJPiPhPBPmPnP6%?QG3P]P;%7Q%9Q%;QAG:<M5C<%:Q%8QD1%6QPUD4,=]52Nn200110F00012110910BA2N\URU50Oe%TjP5E@P2P^PO1I<DPkPLP>PwPED17Ol=JSKP1P8P;POPaPbPcPdPBPePfP6PoG3=2Ngn200110F00012010910BPRPVn10110F00031010D0000=0OURoePoe%KMRoP3E@P0PIPOPoP1PHP?POP6P2P^POPqPrPsPuPvD19O_5=J`tP1P8P;POPaPbPcPdPBPePfP6f@#?G3=2Ngn200110F00012010910BPRPVn10110F00031010D0000n200110C00012010?10@PFPO%VMPRPVn0100000020000n10110F00021010C00=0OUe%PMP9E@AQS\M=0OUe%<\,BSP7E@1lS\=0OUeW7W8W5W6W0W1WDW9WBWEX:4WCo"). Qed.

(* [comment removed for export] *)
Lemma self_jump_account_fix : forall segs ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  mi_account_step segs ms model = MachineOk (ms, model).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "h03immh15modelh22msh32rdh44segsh52szh61wp;1p;3p;2p;4p;<p;5g00;@j1DTg00?Rj10Tg00@7j12Tg00@Uj13Tg011Ij16Tg00?0j14Tg011nj1;Tg00KVj19Tg00<@j31Tg0134j18Tg0141j27Tg00Baj25Tg0153j1:Tg00A8j2CTg0163j1BTg016dj2ATg00^ij4<Tg017Pj1=Tg0188j2>Tg01Thl<?Tg01V5j5@Tg00`P#Dg00_Ig00L8g00Ln#0R0#0#0#0#0R1#2#3R2%60R0#2#3%00#6#2R0#3g010MR3%01#2#3R1#4f5R4#;%9131%42f7R1f6R5#8'7f4R6,5231g01R@R2%:4g01R`31g01S@R7/C3R8#4%B5P7P31A46f3R7C<,5831%=5g01Sl5121>05g010k513f<R3f;R0f:P0P3P0f9f8P1P5P4P6P7f2f1f0M<?D@UUUUUUW5W0W3W6W1W2W4o"). Qed.

(* [comment removed for export] *)
Lemma step_j_self : forall segs regs pc mem rom w (rd : reg) (imm : bv 21) sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"] "h02Hdh12Heh22Hfh32Hih43Hx0h53immh61mh73memh82pch92rdh:4regsh;3romh<4segsh=2szh>1wp;1p;2p;3p;4p;5p;<p;6g00;@j1MTg00?Rj11Tg011Ij16Tg00@7j12Tg00@Uj13Tg008Wj2FTg00?0j14Tg0141j2ATg00Baj2:Tg00<@j30Tg0153j1=Tg00A8j2<Tg0163j1;Tg016dj2LTg00^ij4KTg017Pj1JTg0188j2ETg009Cj1DTg00U6j17Tg01WDj58Tg00;`j1CTg00WCj3BTg00XJj25Tg01X<j2@Tg00<Zj29Tg00V>j2?Tg011nj1GTg01Thl<HTg002jj6>Tg01YFj2ITg00`P#Mg00Ln#1R0#6R1#2R2%10#1R0#1#1R3#1#2#3R4'F%20#3#4\4R0%23#3R3%32%11#6#2R1#3g010MR2%43f8R5f6R6'Af3R7,:330g01R@R3f4R8#=g01R`30g01S@R9/<2R:#4f5R;#;P9P21L87f2R9CK,::30%J;g01Sl5031E1;g010k502g00_IR2#DR1#7R3p,2fxR:f<R<f;R=f:R>f9D8R?g00aO#C5B2,51%72R1f0R@,@2P:f=R:P<P=P>D8,5230X63152?R2,911?:?P:P?P5f7P6P;%44%G?'9P8P7P9f1P@M<HE>1I:?=012eW3W4W0W1W2W=W5W9W>X;0W7X84W:W<o"). Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition silent_loop (P : config -> Prop) : Prop :=
  forall c, P c ->
    m_halted (cfg_model c) = None /\
    ms_svc_pending (cfg_ms c) = None /\
    exists ms' model',
      mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
      P (mkCfg ms' model').

(* [comment removed for export] *)
Lemma silent_loop_cycle : forall (cs : list config),
  (forall c, In c cs ->
     m_halted (cfg_model c) = None /\
     ms_svc_pending (cfg_ms c) = None /\
     exists ms' model',
       mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
       In (mkCfg ms' model') cs) ->
  silent_loop (fun c => In c cs).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h01ch11Hh22csh36model'h43ms'p;1p;3p;2p;4g00;@j1DTg01ZBj33Tg00?Rj10Tg00@7j17Tg00@Uj1CTg00?0j1?Tg01ZYj16Tg00h\j1;Tg00KVj1:Tg00<@j31Tg01[Oj14Tg011nj18Tg00A8j29Tg00U6j1BTg00]mj3ATg00^ij4@Tg00XJj2>Tg01\Bj2=Tg00l8j22Tg01]7j25Tg01]Qj1<Tg01^RR0#Df0R1f1R2530g00Ln#0#0#0#0#0#0#7#CR3#?R4%62#;%:3R331%42#8=143g00_IR3g00L8R41934R5#Bp,4segsf3R6#4%663AP3P4P2P1C@,>5311=21f4530'2X34'5X43'5'2'2[^00P2P1O1X00f29301X00#<eW1W2o"). Qed.

(* [comment removed for export] *)
Lemma silent_loop_sstep : forall P c evs to,
  silent_loop P -> P c -> sstep segs c evs to ->
  evs = [] /\ exists c', to = SNext c' /\ P c'.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh12H1h22H0h32c'h42H3h52H2h62H4h75Hsteph82H5h91mi001mh:2H6h;6model'i016model'h<1li021lh=1si031sh>1eh?6model0h@3ms'i043ms'hA3ms0hB2tohC4HacchD3HeqhE3evsi053evshF3HP'hG7model'0hH2x8i062x8hI3effi073effhJ4evs0hK2H7hL2HPhM2HhhN4HsvchO1ci081chP5HloophQ1PhR1ahS4codei094codehT5modeli0:5modelhU7model''i0;7model''hV2msi0<2mshW4ms'0hX3sigi0=3sigi0>9cfg_modeli0?6cfg_msi0@1oi0A1pi0B6resulti0C1xp%0p%1p&0p;1p;4p;2p;3p;6p;9p;7g00;@k10;Tg01]Qk10:Tg01_GR0j43Tg00?Rj1^Tg00@7k109Tg00@Uk106Tg00?0S00j1zTg01ZYj1<Tg00h\j1CTg00KVj1yTg01[Oj1JTg011nj1BTg00A8R1k200Tg00U6S01k108Tg01\Bj21Tg01]7R2j2OTg00;`k103Tg00<@j30Tg01`;j1FTg00l8R3j25Tg00]mj3MTg0017j6@j7ITg002Mj6oTg00<Zj2jTg00>Uj4}Tg01a1k407Tg002jl9|j6tTg00[]k105Tg001Sj4>Tg001oj62Tg00=Tj2bTg00\ek104Tg00Baj2;Tg01aKj3aTg01bAj1YTg00AXj2\Tg01cGj2iTg01d@j1PTg01e7j1DTg01ejj3gTg01fej2WTg01g[j2[Tg01hQk102Tg00^ij4uTg00XJj2vTg01iIj4{Tg01jAj1xTg00=4j3wTg008:j3~Tf2R4g00_IR5g00L8R6f1R7f0R8Cu'vp=?f5R9f4R:f3R;#J;M4;07/58p=T1O68p=ZA0;47/58p=E%C7=048p=7g01k>R<?078p=hg01^RR=/O8,57p=8%B7=048p==%<89M47p>01A0<47/58p=4A0;471O=8'5p=6f6R>AM9:;P5P6P7P8Cu,v430p=AA0=78p=G%F7=0<8p=XP=P6P;P4P7P8Eop=eA0678p=:P=P5P;P4P7P8Eop=dA0578p=91O=8p=V1147#F=0<8p=NP5P6P7P8Cup=q1v7890;4p=pP6P:P;P4P7P8Etp=UP5P:P;P4P7P8Etp=Qg01l4S02=0<8p=KP:P;P4g01TLP7P8E@p=cP<Q02P:P;P4P7P8FIp=nP<Q02P;P4P7P8E@p=mg01ljR?P4P7P8C{9g:;p=R1;7890;4p=]%x7/18p=l1i78#xp=k1178#Fp=`11;4#F=0<7/58p=SP?P4P7P8C{p=fAa:;4?g78p=Lg01mhR@1W47;w8p=sA~@47=0;8p=_Aw@789~@4p=H1[47=w@8p=rp-0S03\=&0;@RA&0:;P:P;O1p,4segsRBP:P;P4C3P4P9P7O2g00Ln#^#^#^#^#^#^$09$06RC#zRD%<9#C%yCREPD%J9#BPE20056RF$08RGPBf7RH%<HA?F78RIf8RJ1178RKO1ETX;6#ZX@5,O5CECEP3%<>=7DEPD%J>#BPEPGPBPJ%<JRLPIf9RMPKO1ETX;6#ZX@5,O5CE&03@R@90A>S04%F8RN,h>S05PMP8O1'5X3='8P8A7DLEPD%JM#BPEPGPBf;RL%<LPIf<ROPKO1ETX;6#ZX@5,O5CEP3f:RP#J==DEPG%JORQ>01BOPIf=RRPKO1CEX;6#ZX@5,O5PAPPP@PRP8O194PNX3=C6P8A=DQEPGPBf?RQ%<QPIf@RSPKO1ETX;6#ZX@5,O5P2P5PGPBPS%<SPIfARTPKO1ETX;6#ZX@5PAf>RUP@PTP8O194UNX3=C6P8PGPBfBRV%<VPIfCRIPKO1ETX;6#ZP2P6PGPBPI%<IA?F48fDR21148O1ETX;6PAPVP@fERWP8O194VNX3=C6P8PGPBPW%<WA?F:8fFRX11:8O1ETP3PGPB%JX%<XPFP9P7FAfGR31197O1PAPXP@fIRYP8O194XNX3=C6P8PGPBfHRZ#J%<ZPFPHP;FAfJR[11J:O1P=fLR\P8O1PBP7fKR]P[C3%<4=7DE%J;==DEPGPB%J:%<:PFPUPPFAPAfOR^P@fRR_P8O194^NX3=C6]C]N]M]7]LP[P^PKO1PB1147fNRKfMR`C311;4#<=7DE11:;S06#J==DEPGPB119:S07#JQ07#<PFPTPRFAP0PB11PMS08,G;fWR090A;1h;0PAfYS09P@Q09f\RaP8O174NX3=C6[[[P;A7D4ERb%B:S0:=0DES0;PGPBP9P:PFP;P4FA11>9S0<112IS0='GfaRc90A@Q0</Xc11MJS0>113XS0?'GP=P6P8P8n0110800012010?10>X>=S0@Q0811Z3RdP8Ce1:M3P=P5P8P7n0110800012010?10>X>=S0A11LPS0B11YZReP7Cd19LY19O[P819R]P\1:U\RffjRg90A@S0C11QUS0D/XgA7DTEQ0;PGPBP9PIPFPVPTFAPAfoS0EP@Q0EfrS0FP8O1S0G74NX3=#VS0HCE]1]2]0]6]4[X951:R]P8PfP`fkRf90A@Rh11SQS0I/XfRi%B_S0J=0DEPGPBfSRjP:PFPIPVFAPAfpS0KP@Q0KfsS0LP8O1S0M74NX3=C6]1]2^0b]6]4X96Q0CP8PhPAP@flRh9NTSRkfQRl=7DERmA=DjERnPGPBfTRoPjPFP2PIFARpA0A:@S0NfqRqftRrP8O1S0O74NX3='8]1]2]0]6X<AP8PkP<11VTS0P#FA7D_EA=DoEPGPBfURkPoPFPWP2FAA0A@@Rs1h:NS0QfuRtP8O1S0R'5X3='8]1]2]0X=<PAP@PBfVRu/1kRvP8PqC3%FdfvS0SP8O1S0T74NX3=,8s]7XEAPB11koS0UP@Q0KC3P<11XWS0V#FRdPB110uP@P8C3%FefwS0WP8O174NX3=,8s]7XB<PBPvP@PdC3PGAMB0uA?FZ3Rd90G8X9GP4fcS0Xf_Rv5?FRePlE@PGPePF1q3XCpPGP5Q01PFP5P8P1P5P6P5P8P7n200110A000120100100feS0YQ0Yn10110000031010B0000X>GfdS0Zf`Re5?FPdP8EoQ0Z/9ZPGP6Q01PFP6P8P1P5P6P6P8P8n200110A000120100100fbR1P1n10110000031010B0000X>GQ0Y=?FcA?FYZP7Eo1:cZ1:1YfgRd/9]P6P]PGPBf]RwPaPFfiRxP8FAf|S0[11g7O1PGA?Ff4PF1q^KCpfPRy,1lS0\#Fp+01@S0]P8O1S0^74NX3=,8s]8]F]CX;6PGPBPaf[RzPFfhS0_P]FAf{R{11x\O1PGA?Fg`PF1qK`CpP5P^f~S0`118^O1PGPBPcPePFP7PyFAPGA?F4lPF1q_lCp11ojS0a#Fp+01CP8O1S0b74NX3=,8s]8]C]FX@5f}R|11^KS0cO1PGPBPePvPFPyP^FAA?FlyR}=0G}Ps11j_S0d#Fp+01BP8O1S0e74NX3=R}#V1jA@P=P}11_lR}%F}R~/h~p+01AS0fP}O11j<~P4C}H07C}W8WCWFPfP;P7P4P8M9|W8WFWCQ0ZP7PuPvP:M9|UUP8O1b0P8O1b0b8W7PqP9P8FIW7PqP>P_FIX8pX5nX1mfmRmP8E@b1X6iPhP8E@b1W4PQP8DUb1W2PUP8DQb2W0P8O1b0P8O1b0W5P4P7P8P9P:P;O6W6W4W5W1W2W0XG6XW5X?6XA5P>P9P:P;P4P7P8O7A7D8ES0CA=D4ES0gAMB;4S0h&05FRi50GQ06Q0I'GS06A0A@wS0i%KwS0j11H>S0k11IV'GS0lQ0@11JHS0mQ0=P8CeS0=1:HIS0nQ0AQ0>11W2S0oP7CdS0p19MWS0q19PXS0rP819L3S0sPZ1:OZS0tffS0u90A@RnQ0u#KS0vA7DQES0wQ0;AMB9TS0x=0GiPAPfP@fnS0yP8O194fNX3=C6S0z]1]2]0]6]4[X951:L3S0{P8Q0tPYA0A@dS0|%KdRdA=DKES0}AMB^:S0~=0GiPAPhP@Q0EP8O194hNX3=C6S10]1]2^0b]6]4X96P8Q0|PAP@Q0_#KS11A7D`ERpA=D^ER~AMBy^S12=0GiS13Q0NQ0KP8O194mNX3=#VS0K'5S14]1]2]0]6X<AP8Q11A7DKES15%ByS16=0DES17AMBlyS18=0GiQ0QPqP8O1S19'5X3=,8sS1:]1]2]0X=<Q13PAP@PBP}P8PmC3%KNRqQ0G'5X3=,8s]7XEAS0GPBQ0\P@PhC3S1;PBQ0dP@P8C3Q0M,5qX3=,8s]7XB<S1<PBP}P@Q02C3S1=PGPiAMBj_S1>A?FvzS1?PGQ1>PiP4C>P`E2Q1?90GiPGPiQ01PFQ03P8g01n^Rig01o;S1@Pin10110000031010B0000X>GA?FeaS1AP8DcPiQ0O,5qX3=,8sS0O/b8S1Bb0bDW7PmP9P8DnW7PmP>PKFIW8X5~X1pPxP8Cmb1X6dQ0_P8E@b1X4nPRP8DUb1W2POP8DQb2W0P8O1b0P8O1b0W5P4P7P8P9P:P;O6W6W4W5W1W2W0X?6XA5P:P;P4P7P8O5Q0CQ0gQ0h&04FRh50GQ06Q0iQ0jQ0lQ0=Q0nQ0pQ0qQ0rP8Q0sPZQ0tQ0vQ0wQ0;Q0x=0GhQ0z]1]2]0]6^4n[X95Q0{P8Q0tPYQ0|Q0}Q0~=0GhQ10]1]2^0b^6d]4X96P8Q0|PAP@Q11Q12=0GhS12Q14]1^2~^0p]6X<AP8Q11Q15Q17Q18=0GhQ1:]1]2]0X=<Q12PAP@Q0GQ1;Q1<Q1=PGPhQ1>Q1?PGQ1>PhP4C>P`E2Q1?90GhPGPhQ01PFQ03P8PiPiQ1@n10110000031010B0000X>GQ1AP8DcPiQ1Bb0bDW7PmP9P8DnW7PmP>PKFIW8X5~X1pPxP8Cmb1X6dQ0_P8E@b1X4nPRP8DUb1W2POP8DQb2W0P8O1b0P8O1b0W5P4P7P8P9P:P;O6W6W4W5W1W2W0X?6XA5P:P;P4P7P8O5%C9S0C=0DES0g1;C99=DHS06AaBJ>S0iPHP9P:P4DRQ0g%z6Rn%YH,\>P6P9C]Q0B11K`'GS0BA0A>f1iRP/lJ/Xf11URS0jQ0\'GS0lQ0@Q0DP}P8CeS0r1:UlS0{Q0AQ0IQ0dP7CdS0I19SjS1219ToS1;P819VkS1=Pu1:IuS1BA0AQrS1A1i4I/lT/Xr%CXS01=0DES1?Q0:1;CXR}50DS1>AaB93S1<PZPXPWPIDRQ1?Pn%YZ,\3S0GP6PXC]PAP{P@Q0`P8O1S1594{NX3=#VS17CES1:]4]5]1]2]0]:]8[X951:VkS18P8Q1BP0A0AStRdfZRp/i2/lV/XtS14%BaS0|1;C3S0}50DS10AaBwZS0~P:P3PXP2DR%C3S0t=0DES0vPn%YY,\ZS0wP6P3C]PAQ0[P@Q0[Q0^74NX3=C6S0;]4]5]1]2^0b]:]8X96Q1AP8PdPAQ0S1izW/lIQ0S'XRdA7DzES0z1;CZS0x9=DwS0sf^R~=aBYS0qPwPZP3P;DR%CZS0p=0DES0nPn%Y[,\YS0=P6PZC]RGPAP|P@Q0fP8O1S0h94|NX3=#VS13CE]4]5]1]2]0]:X<AQ14P8PdP<1kaX/`2A7DaES1C1;CY9=D~S1DAaBv[S1EP~PYPZP{DR%CYS1F=0DEPn%Y],\[P6PYC]PAQ0`P@Q05Q0e'5X3=#VS1GCE]4]5]1]2]0X=<Q0zQ0sQ0qPwPZP3fzS1HDRQ0nP<1kc]/`YRdPB111cS1IQ0`P8C3PAQ0]P@Q0Z/kKP\PNQ0bCSX3=C6]7XB<PB11ceS0]P|PdC3PDPE%C]Rd1;C`RFPDPdPEP4C>S0`PDPdPEPFP4PDPE%CcRhPFPDPhPEP9C>PDPhPEPFP9PDPEPdPFQ0`PDPdPEPFP4PDPE%B1RhPFPDPhPEPwC>P:E2E2E2E2E2E2E2A0DEFS0`PDPEQ00PCQ03P8PiQ1@n10110@00021000000X>DS1J1;CKRhP8DcS1KPiPAQ0fP@Q0Y/k^P`PNp+01DP8O1S0fCSX3=C6/b8b0bDW7Q0[P>P~FIXKGW6W4W5W1Q0WP8E@b1W:PTP8Etb1W8P2P8DUb1W2PIP8DQb2W0P8O1b0P8O1b0W6P4P7P8PHP>P9P:P;O8W:W8W6W4W5W1W2W0XJAXU6XG6XI?XHCX?6XA5PLPPPMPJPHP>P9P:P;P4P7P8O<A7D:ES1A1;C:9=D>PBPHP9P>Af:;4DLQ1A%Y>,\9%y6RG50nQ0811\]'GS14A0A@xS1L%KxS1M11ROQ0c'GS0cQ0@Q0j11y^P8CeS0j1:R^S1NQ0AQ0DQ0\P7CdS0\19QlS0D19S_S1OP819TjS1PPo1:VoS1QQ0F90A@S1RQ0F#KA7DWES1SQ0:1;CWS1T50DS1UPBP9PXP3AfW2IDLS1VQ1S%Y3,\X=0nGPAfyS1WP@Q1WQ0[P8O174NX3=C6S1X]4]5]1]2]0]:]8[X951:TjS1YP8Q1QPkQ0L90A@S1ZQ0L#KS1[A=Dp}S1\PBPzP3P:AfXW2S1]DLS1^Q1?Q0G=0nGPAQ1HP@Q1HP|P8O174NX3=#VS0GCE]4]5]1]2^0b]:]8X96Q1RP8Q1ZPAP@%KrS1ZQ09=7DES1_Q0}9=DzS1`PBPaPZPzAf3XWS1aDLS1bQ0vQ0w=0nGS0wQ04Q17'5]4]5]1]2]0]:X<AQ1[P8Q1ZA7DpES1ZQ0|Q0x50DS0xPBPwPYPaAfZ3XS0|DLS17Q0nQ0==0nGQ05Q0^'5X3=,8s]4]5]1]2]0X=<Q1_Q1`Q1bQ0vQ0wPAP@PB11evS0nP8P{C3Q0h,5qX3=,8s]7XEAPB11v~S05P@Q1HC3PBQ0]P@P8C3Q0e,5qX3=,8s]7XB<PBQ0nP@Q02C3PDPEPdPFPDPdPEP;C>RGPDPdPEPFP;PDPE%CeRnPFPDPnPEP>C>PDPnPEPFP>PDPEPdPFPGPDPdPEPFP;PDPE%BcRdPFPDPdPEPaC>P9E2E2E2E2E2E2E2Q0`Q1KPiQ0b,5qX3=,8s/b8b0bDW7P{PHP8DnW7P{PJPaFIWKW6W4W5W1PtP8Cmb1W:PrP8E@b1W8PIP8DUb1W2PVP8DQb2W0P8O1b0P8O1b0W6P4P7P8PHP>P9P:P;O8W:W8W6W4W5W1W2W0XJAXG6XI?XHCX?6XA5PPPMPJPHP>P9P:P;P4P7P8O;Q0gQ06Q0iPHP9P:P;DRS0iQ0C1;C;S1A50D%P>=0DEQ0BPAPH%DJ=s>@PfC_ANRMfQ0lQ0rQ0{Q0IQ12Q1;P8Q1=PuQ1BPAPS%DTS1==sQ@PrC_S12AN4VrQ1?Q1>Q1<Q1]7gZQ011;C2S1]50D%P3S01=0DEQ1:]4]5]1]2]0]:]8[X95Q18P8Q1BP0PAPT%DVS1B=sS@PtC_R0ANpItS1?Q10Q0~Q1a7g:Q0tQ1T50D%PZS0t=0DEQ0;]4]5]1]2^0b]:]8X96Q12P8P0PA%DI,WT=HV@Q0S9Nz2R0Q0zQ0sQ0qQ0|7gwRdQ0p=0D}RG%PY=0DERnQ04Q13'5]4]5]1]2]0]:X<AQ1?P8P0P<1`aWQ1CQ1DQ1EP~PYPZP3DRQ1FQ0}50D%P[=0DEPA%D]S1F,WY=H[@S1EP@Q1GCE]4]5]1]2]0X=<Q0zQ0sPA%D[S1C,WZ=HY@RaPBQ1IP8P|C3PA%D\S1D,W[=H]@R0P@Q0ZP`PNQ0bCSX3=C6]7XEAPBQ0]PaQ0[C3P<1`1]RaPBQ0X/11P0P8C3PA%D`,W]=H\@P@Q0YPKPNQ0fCSX3=C6]7XB<PBQ1IQ1EPaC3PDPE%P\RaPhPDPaPEP4C>S1EPDPaPEPhP4PDPE%C1R0PhPDP0PEP>C>PDP0PEPhP>PDPEPaPhQ1EPDPaPEPhP4PDPEQ0X#BRaPhPDPaPEP~C>P9E2E2E2E2E2E2E2A0DEhPDPEQ1J1;C^P8DcPiPA%DK,W\=H`@P@Q0uP^PNp+01EP8O1CSX3=C6/b8b0bDW7P|PHP8FIW7P|PJP~FIXKnX6GX4dW5W1Q0WP8E@b1W:Q0SP8E@b1W8P2P8DUb1W2PIP8DQb2W0P8O1b0P8O1b0W6P4P7P8PHP>P9P:P;O8W:W8W6W4W5W1W2W0XSCXJAXG6XI?XHCX?6XA5PLPPPMPJPHP>P9P:P;P4P7P8O<Q0gQ06Q0i%P9Q1A50DQ14PAP>%DH=r9@PxC_ANOJxQ0cQ0jQ1NQ0\Q0DQ1OP8Q1PPoQ1QPAPQ%DS=rU@Q0FC_RxQ0F9N4TQ1SQ1UQ1V%PW1;CIRd50DPAfxRGP@P{P8O194GNX3=C6]5]1]2]0]8]6[X95Q1YP8Q1QPkPAPSQ1==rQ@Q0LC_RQfXRGQ0L7NVR{Q1\Q1^%PXQ1]50DQ1X]5]1]2^0b]8]6X96P8PQPAQ1B,[S=HT@Q09?NIrRQQ1_Q1`Q1bQ01Q1T50DRnPAP9P@Q0GCE]5]1]2]0]8X<AP8PQP<1`p2Q1ZQ0xQ17Q0t=0D}PA%DY,[3=HZ@RpP@Q15949NX3=C6]5]1]2]0X=<Q1_Q1`Q1bPA%DZ,[X=H3@RQPBQ05P8Q1HC3PAQ1C,[Z=HY@R|P@PcP]PNQ0^CSX3=C6]7XEAPB11~wPQQ1WC3P<1`vYRQPBQ0nP|P8C3PAQ1F,[Y=H[@P@P1P\PNQ0hCSX3=C6]7XB<PBQ05PpPQC3PD1;C\R\%BeRePEPDPeP\P:C>PDPePEPEPzPDPE%CvRePEPDPePEP9C>P9E2E2E2A0D\EPDPFQ00PCQ03P8Q1@Pin10110@00021000000X>DRFPEP8DcPiPAQ1D,[[=H]@P@Q0XP`PNQ0eCSX3=C6/b8b0bDW7Q1HP>P8FIW7Q1HPHPzFIX:nW4W5W1PtP8E@b1X8{PrP8E@b1X6xPIP8DUb1W2PVP8DQb2W0P8O1b0P8O1b0W4P4P7P8P>P9P:P;O7W8W6W4W5W1W2W0XXCXJAXG6XI?XHCX?6XA5PPPMPJPHP>P9P:P;P4P7P8O;A7D7E1;C79=D;PBP:P4P;&02?R?DLQ07Q0P'GA0A@v%KvQ0mQ0o'GQ0@Q0>Q0VP8Ce1:JWQ0AQ08Q0?P7Cd19P319LZP819OYP[1:R[R[Q0_90A@RZQ11A7DSEPDQ0:PCPSC]PBP9PTPVP?DLPAPmP@Q0KCE]1]2]0]6]4[X951:OYP8P[P]Q1LQ1MPDQ16PCPTC]PBPlPVP:P?DLPAQ0yP@Q0yQ1974NX3=C6]1]2^0b]6]4X96P8Q1LPAP@%KgRbA7D^ER^1;CV9=DlRVPBP_PIPlP?DLRIQ0NQ0H'5]1]2]0]6X<AQ1MP8PbA7DyEQ0J=0DdPBPjP2P_P?DLQ0QQ0M'5X3=,8s]1]2]0X=<PAP@PBQ0aP8Q0EC3Q0O]7XEAPBQ0dP@Q0yC3PBQ0UP@P8C3Q0R,5qX3=,8s]7XB<PBQ0aP@Q02C3PDP}%BkRkPEPDPkP}P;C>PDPkPEPEPyPDPE%CoRoPEPDPoPEP:C>P:E2E2E2A0D}EPDQ0}PFPEP8DcPiQ0T,5qX3=,8s/b8b0bDW7Q0EP9P8DnW7Q0EP>PyFIX8IX5VX1^PfP8Cmb1W6PgP8E@b1X4ZPUP8DUb1W2PRP8DQb2W0P8O1b0P8O1b0W5P4P7P8P9P:P;O6W6W4W5W1W2W0XHCX?6XA5P9P:P;P4P7P8O6n10410810210300000087110<10:1041010000000005110<10:0000000005110<10:000000000<110<10:10610710110;105000000000000000;110<10:106107101105000000000000000<110<10:106107101105109000000000000000;110<10:10610710110510=0000000000006110<10:106000000000Q0>,G4A0A4u1h4uPAPGP@PzP8O194GNX3=C6[[[X=<X<AXO=Q0<P_PlO3P8Q0k,j=1jAj1j<_O3b0WCWNWMW7WLXT6XV5P7P8O2n0110800012110?10>PXPWPTPRP7O5WFWCP7P8O2n2001000000121000000W0X;6P7P8O2n200100000012110C000W0X@5P7P8O2n200100000012110C000W0WNP7P8O2n2001000000121000000W0WMP7P8O2n2001000000121000000bRW7WLWPXB<WEXO=WQo"). Qed.

(* [comment removed for export] *)
Lemma star_case : forall c tr c', star segs c tr c' ->
  (tr = [] /\ c' = c) \/
  exists evs c2 tr2,
    sstep segs c evs (SNext c2) /\ star segs c2 tr2 c' /\ tr = evs ++ tr2.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h03tr2h12c2i002c2h23evsi013evsh31ci021ch41Hh55Hsteph65Htailh72c'h82c1i032c1h92c3i042c3h:2tri052tri062c0i071lp;1p;4p;3p;2g00;@j1?Tg01oWR0j45Tg00;`j1<Tg00<@j31Tg00l8j20Tg01`;j16Tg01_Gj44Tg01]7j22Tg020Jj2;Tg00<Zj27Tg00>Uj48Tg020dj3:Tg01a1j49Tg021>j3>Tg008:j3=Tg01mhR1f1R2f0R33=p=3g01^RR4%?1R5p,4segsR6f2R7P2P3C5P0P6%<1R19157f3R09142'0P6f6R8P7%62R9C4P6P2P3f4R:C5R;f5R<1373R=515'0'0X05,25X14,24X25,25';P3A1511R>A1433R?'0P6P0P7P9C4P6P2P3P0C5A151='0'0X05,25X14,24X25,25P>P?17511743C83:X34P3O1P6P:P0%67C4P6P0P7P2C513<0R?=151A1478'0P6f9P7P9C4P6P2P3P<C5f8R1/38=15='0'0X05,25X14,24X25R=,25P5P=P<P4P6P1f7R1P9C4131<1313515,0;'0X05,25X14P:P5P6P1P8%6<C4P6P<P3P0C5138:1383515'0'0X05P0P6P8P<%6:C4P6P:P0P7C5R6A15??R1'0P2P6P1P3175?C8C8C9C9C93>W6W5X94X05X14X25X84P8P<P:P0P7P2P3O7n10410210710600000021010271103101100105104000000W4X74W:W3o"). Qed.

(* [comment removed for export] *)
Lemma silent_loop_star : forall P, silent_loop P ->
  forall c tr c', star segs c tr c' -> P c -> tr = [] /\ P c'.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh12c'h25Hstarh31ci001ch42trh53HP2h65Hsteph72IHh82HPh91ah:3c2'h;3evsh<3HP3h=3Heqh>5Hlooph?1Ph@2c2hA2c3hB1ei011si021xp;1p;4p;3p;2p;7p;6p;8g01]Qj1DTg00;@j1CTg01oWj46Tg00;`j1:Tg00<@j32Tg00l8R0j23Tg00<Zj2<Tg00>Uj4;Tg01`;j10Tg01_Gj48Tg021Xj79Tg01]7R1j27Tg002Mj6BTg002jj8=j7?Tg0017j7>Tg022_j8@Tg008:j3ATf3R2f2R3f1R432f0R5'3p=1g01k>R6?245p=4g01mhR7?A45p=5g01^RR8p-0[%D5%C7R9p,4segsR:P3P4P5C6P:f8R;P3O1%:7R79293R<f9R=P4O1'3[X18X49X38f6R>P5O1A2977R?f7R@P4O11<97P5C;W8X38P:f4RAP2%03C8P:P2P3P4C6f<RBPAO1P9PAP7f=RCP2O1C1[PCP@O1f>P;P@%0>PCP5P2F9P9P@P7%0@%05RD'4f?REP5O1'3X18,78C1P0A29;7%0;/4Df@R;P5O1'3X18,78P915=@P7P;P>O1C1P5f:R==297P9P7P:PCP5f;RF#0C8%0C/4DfERCP5O1'3X18RG,78P9153BP7PCPFO1RHC1[]6X;9P:PBP7%0=C8%0B/4DfDR=P5O1'3X18,78P1P8PGP9157BP7PHC1P5%0E/4DfGRDP5O1'3P0%0;%04'4fHRHP4O1P9157;P7fIR;PEO1C1P5fBRE#0%02'4fKRBPAO1P6P8P6P8P5P5PCn0110100021010000XB6%0=f5R6#0P4EBA28=6A28C>P8fFR>fOR6P5O1P9157DP7fPP>O1R=C1]5X:8fNP>O1PEP5O1P9P>P7P6PCO1C1P0A29D7P=P9157HP7fQPDO1C1P5A29;7P9P7P:fLRHP5fJR=C6fUR0fMRCO1fVPHO1R6,3<[P91572P7fWPCO1C1\6]7]2X49P:PBP7P;C6fTPHO1P0PBO1RB,3?[P4P@O1X<BW7W2P=P5PDP>G=W0P4P5O2n2001000000120000000b9W5P@P5P3F>W0P5O1b0W5W=P4P5O2n2001000000120000000W0X:8P4P5O2n2001000000121102000W0W6PFP5P@F?W0P4P5O2n2001000000121000000b9W8W7W2W6XA8X49X@8X;9X38P2P3P4P5G@W2X18W4X38W>W?o"). Qed.

Lemma silent_loop_star_nil : forall P c tr c',
  silent_loop P -> P c -> star segs c tr c' -> tr = [].
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02HPh15Hlooph25Hstarh31Ph41ch52c'h62trp;1p;4p;3p;7g00;@j16Tg01]Qj15Tg01oWj40Tg00;`j11Tg00<@j34Tg023Tj72Tg024Zj33Tg01^RR0p-0[g01mhR1#6R2f3R3#5f4R4P3O1p,4segsP4P3f2R5C0%119424f6R2P3O1P2P5f5P4P3f0f1F233W2W0W1X50W6X40W3o"). Qed.

(* [comment removed for export] *)
Lemma silent_loop_no_error : forall P c,
  silent_loop P -> P c -> ~ reaches_error segs c.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh13evsh22c'h31ci001ch42_Hh51ah62trh72HPh83HP2h93Heqh:4Herrh;5Hlooph<5Hstarh=1Ph>3_H0h?2c2h@1ei011si021xp;1p;2p;4p;7p;3p;6g01]Qj1?Tg0255j2>Tg00;@j1:Tg01oWj42Tg01_Gj44Tg00l8R0j20Tg01]7R1j21Tg023Tj79Tg00;`j18Tg00<@j33Tg021Xj77Tg01`;j15Tg0017j6=Tg00=Tj2<Tg025oj1;Tg01k>R2g01l4R3f0R433p=6g01^RR5p-0R6[f1R7#?f2R8P7O1p,4segsR9/>8R:P1g01mhR;#:R<P9f6R=P8P7C2P9P7P4P3C4R>'0X1<,1<X35,15X6<g01n^R?P4P9f8R@P8P7C2/0>X1<,1<X35,15P1P5P9f9RAf3RBP7C2/0>X1<,1<X35P?P4P9f;RCf5RDP7C2/0>X1<,1<P1P<P9f<P=P8C2P9P8P4P3C4'0X1<P?P4P9f>R8P@f4R=C2P9P=P4P3C4'0P0P9f?PAPDC2P9PDP7P3C4P?P4P9fAR>PCf7C2P9P@P=P3C4fDR@fBfCf=R9PAP7P>F9%8;R;93<9R>P@PAO1'0P0A3<8;fEf:RAO1P?P4f@=3<;fHP9O1fIP8PAP3fGP4PDF7A3<A;%54#6RAfJP4O1'0X25,15'0P0A3<C;fKP4O1,0AX25,15P?P4fNP4O1,0AX25,15P1P5fOP4O1,0AX25P?P4fQP4O1,0AP0%57#6fRP7O1P?P4%5B#6fUP=O1P2P3P2P6P4P?g01o;n0110100021010000X@2g01TL%5DP7E=P?1<?4b0W>W9P7P4O2n2001000000120000000W0X25P7P4O2n2001000000120102000W0X4>P7P4O2n2001000000120000000b5W8W4P7P4O2n2001000000120000000b5W:W<P7P4O2n2001000000120000000W0X1<P7P4O2n2001000000120102000W0X?5P7P4O2n2001000000121102000W0X6<P7P4O2n2001000000121102000W0%;:eW7W;X35W=o"). Qed.

(* [comment removed for export] *)
Lemma silent_loop_no_unmodeled : forall P c,
  silent_loop P -> P c -> ~ reaches_unmodeled segs c.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02HPh15Hlooph21Ph31cp;1p;4p;3g01]Qj12Tg026Hj41Tg027Rj30Tg01^RR0p-0[f1R1#2f2R2P1O1p,4segsf3P2P1f0C1702W0W1X30W2o"). Qed.

(* [comment removed for export] *)
Lemma silent_loop_obs_iff : forall P c,
  silent_loop P -> P c -> forall tr, obs_trace segs c tr <-> tr = [].
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh11ch23tr'h34Hpreh42trh52HPh65Hlooph75Hstarh81Ph92c2i001xp;1p;3p;4p;2p;7p;6g01]Qj1?Tg00;@j1>Tg028Tj34Tg00;`j16Tg00<@j32Tg01oWj41Tg00l8R0j23Tg01]7R1j25Tg029Jj77Tg0017j68Tg02:Tj39Tg02;[j2:Tg002jj6=Tg00>Uj4<Tg003Hj3;Tg01mhR2f1R3f0R43;p=0g01^RR5p-0[%?3f2R6P3O1%>2R7p,4segsR8f3R9;44R:%62R;9273[A274;R<f4R==483[P1P7P8f6R>P3P4C11093'3X15,55X27A276;P4P8f8R?P3P4C1f5R@/03'3X15,55P1P5P8f9R1P6P4C110>6'3X15A27>;P4P8f;P=P4C110?='3P0P8f<R0P@P3C1101@f:=27;P4P8f>R>f7P9C1100?P7P110>4X27P4P;fAf@P1P@f?P>P3F7E8f=/0;A92>4b3W3W7P3P4O2n2001000000120000000W0X95P3P4O2n2001000000120100000W0X27P3P4O2n2001000000120100000X0:P7P;A48@4X471:8=P3P4E=X0<C<W4W5W6X15W8o"). Qed.

(* [comment removed for export] *)
Lemma silent_loop_not_all_errors : forall P c,
  silent_loop P -> P c -> ~ all_traces_error segs c.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h06model'h12HPh23evsh33ms'h42c'h51Hh64Hacch72Hhh85Hnexth95Hprogh:4Hsvch;2IHh<1ci001ch=2toh>3HP'h?4Hallh@5HloophA1PhB1ahC5modelhD2msi019cfg_modeli026cfg_msi031xp;1p;2p;4p;3p;8p;6g01]Qj1PTg02<Uj2ATg00;@j1HTg01_Gj4;Tg01]7R0j24Tg01`;j1OTg00?Rj1:Tg00@7j1GTg00@Uj1ETg00?0j1DTg01ZYj10Tg00h\j1=Tg00KVj1BTg00<@j33Tg01[Oj15Tg011nj1<Tg00A8j2NTg00U6j1MTg00XJj29Tg01\Bj22Tg00l8R1j2?Tg00;`j1ITg02=Tj8JTg02>Hj6KTg025oj1LTg00]mj3>Tg00^ij4CTf2R2f1R3#5f0R43>p=6g00_IR5g00L8R6P3P4CCp=7f3R7?323/?4p=11464p=8%049>23p=Ff4R8A>723;34p=@g01^RR9p-0[%P3P2P3O1p,4segsR:/A2R;P:f5R<P4O1g01n^R=]1X<9g01mhR>#HR?g01k>R@P:P2P3P4C;X=@'4X2?'4RAP:P7P3%O4RBC;1A:3RC[^49^2?RDP:P8P3PBC;REf:RFP3O1P=]1[^49^2?f8RGP7O1f7RHP8P4O2g00Ln#:#:#:#:#:#:#G#ERI#DRJ%08#=%BIRI33RKPJ%58#<PI1N56RL#MRMf6RN%0N56:RO1734,9LRPf;RQ1234RRO1C1X06#8X35,45C1'?P1%0<#==3JI%5<#<=3JIRSPM%0HRT96:HPPf<RUPRO1C1X06#8X35,45'?P=P4%=T=3JIPJ%5G#<PIPM%0F96:FPPf?RFPRO1C1X06#8X35,45C1P1f9#5#<=3JIPM%5QRT=F:QPPf@RVPRO1C1X06#8X35,45P=P4%<T=3JIPMf>RT%0T56:PPfCRTPRO1C1X06#8X35,45P0P5PM%0F96:FPPfDRWPRO1C1X06#8X35P=P4PMfARX%0X56:PPfFRPPRO1C1X06#8P0P6PMfBR0%0056:1724,9LfGR01224O1C1X06P=P4PM%0W96:W1784,9LfIRR1284O1C1P1PMP:fER1#5%0117<3,9LD@fJ12<3O1P=P4PMP:%50%0017H7,9LD@fM12G8O1P9fTP3O1P=]1\E^49^2?fRP7O117VU,9L93MOP=]6^:S^7K]1];^8D^9APRP:1272P3P4C;X=@,4@X2?,4?P:1287R@P3PBC;PC[^49^2?P:12<8RCP3PBC;fWP3O1P=]1[^49^2?fUP@O1%0C#==3JI12N<#5#<=3JIPMP:12HNRN#5%0N17TF,9LD@P8%I>12WVP:PGPHPWPVP2P3P4GJPQO4W6W:W7W1W;W8W9XC6XD5P3P4O2n01100000120102101fHP0PPP1PXf=P3O7W>W6P3P4O2n2001000000121000000W5X06P3P4O2n2001000000121103000W5X35P3P4O2n2001000000121103000W5W:P3P4O2n2001000000121000000W5W7P3P4O2n2001000000121000000bBW1W;W8W9X<9P7P4P3EKW?%L;eW1W@X<9WAo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_spin : machine_state -> Model -> Prop :=
| ts_spin : forall ms model,
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms, model) ->
    to_spin ms model
| ts_step : forall ms model ms' model',
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    to_spin ms' model' ->
    to_spin ms model.

(* [comment removed for export] *)

Lemma ts_spin_no_access : forall ms model,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []) ->
  to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h05Hsteph14Hsvch25modelh32msp;1p;3p;2p;5p;4g00?Rj10Tg00@7j1>Tg00@Uj13Tg00?0j12Tg011nj1=Tg00KVj1:Tg00<@j31Tg009Cj14Tg00U6j15Tg00V>j26Tg00;`j17Tg00WCj38Tg00XJj29Tg01V5j5<Tg02?Ij4;Tg00_IR0g00L8g00Ln#0#0#0#0#0#0#>#3R1#2f1R2#=%:131%40R1#5p,4segsR3f2R4'6g00aO#79804,9131f3R1P4P2P3P1P4P1f0D<C;W0W1W2W3o"). Qed.

Lemma ts_step_no_access : forall ms model ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  to_spin ms' model ->
  to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h05Hspinh15Hsteph24Hsvch35modelh42msh53ms'p;1p;3p;2p;5p;7g00?Rj10Tg00@7j1?Tg00@Uj13Tg00?0j12Tg011nj1>Tg00KVj1:Tg00<@j31Tg009Cj14Tg00U6j15Tg00V>j26Tg00;`j17Tg00WCj38Tg00XJj29Tg02@Hj2=Tg01V5j5<Tg02AGj7;Tg00_IR0g00L8g00Ln#0#0#0#0#0#0#?#3R1#2f2R2#>%:131%40R1#5p,4segsR3f3R4'6f1R5g00aO#7580,91311=24f5R1f4R6P4P6P2P3P1P6P4P5D<f0F;W0W1W2X50W3W4o"). Qed.

(* [comment removed for export] *)

Lemma ts_spin_no_lazy : forall ms model,
  ms_svc_pending ms = None ->
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms ->
  to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01mh15Hlazyh25Hsteph34Hsvch45modelh52msi003ms'i011xp;1p;3p;2p;6p;4g00?Rj11Tg00@7j1FTg00@Uj1=Tg00?0j19Tg011nj1ETg00KVj1CTg00<@j32Tg00A8j27Tg00;@j1;Tg00Eoj1:Tg00;`j18Tg00U6R0j14Tg01YFj25Tg00XJj20Tg00[]j1DTg00\ej1BTg00<Zj2?Tg002jj66Tg00]mj3>Tg02BFj4@Tg02?Ij4ATg00^ij4<Tg00_IR1g00L8R2f1R3f0R4C<p=3g00Ln#1#1#1#1#1#1#F#=R5#9%E3%C5321755R5#;%:3%8532%41R5p,4segsR6f3R7'5101732f4R8P7f21712R9#4R:P0P1P:1568R;1348,09%D9R<%B9R=n1011010003101000000f5R>/38,09R?92:4X0:P51018P0P1P:P4134>,09P<P=n1011010003101000000=2:?X051387,09,?:P;P4E6A>687P6P8P7P3C@E6CAW2W1W3X42X51o"). Qed.

Lemma ts_step_no_lazy : forall ms model ms',
  ms_svc_pending ms = None ->
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_spin ms' model ->
  to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01mh15Hlazyh25Hspinh35Hsteph44Hsvch55modelh62msh73ms'i003ms'i011xp;1p;3p;2p;6p;4p;7g00?Rj11Tg00@7j1GTg00@Uj1=Tg00?0j19Tg011nj1FTg00KVj1CTg00<@j32Tg00A8j27Tg00;@j1;Tg00Eoj1:Tg00;`j18Tg00U6R0j14Tg01YFj25Tg00XJj20Tg02@Hj2ETg00[]j1BTg00\ej1@Tg00<Zj2?Tg002jj66Tg00]mj3>Tg02BFj4ATg02AGj7<Tg00^ij4DTg00_IR1g00L8R2f1R3f0R4CDp=3g00Ln#1#1#1#1#1#1#G#=R5#9f2R6#F%C5321755R5#;%:6%8532%41R5p,4segsR7f4R8'5101632f3R9/E8f6R:f5R;P8P;P91712R9#4R<P0P1P<157:R=134:,09%B9R>%@9R?n101101000310100000013;:,09R@92<4X0<P51018P0P1P<P4f7,34,09P>P?n1011010003101000000=2<@X05138;,09,?<P=P3E6A>7:;P7P:P;P6CAE6P4F<W2W3W1W4X71X52X61o"). Qed.

(* [comment removed for export] *)
Lemma ts_spin_of_step_j : forall ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h03immh15modelh22msh32rdh42szh51wp;1p;3p;2p;4p;<g00?Rj10Tg00@7j13Tg00@Uj12Tg011Ij16Tg00?0j14Tg011nj1<Tg00KVj1;Tg00<@j31Tg0134j19Tg0141j28Tg00Baj25Tg0153j17Tg00A8j2:Tg0163j1CTg016dj2BTg00^ij4ATg017Pj1=Tg0188j2>Tg01Thl<?Tg02CJj4@Tg00_Ig00L8g00Ln#0R0#0#0#0#0R1#3#2R2%60R0#3#2%00#6#3R0#2g010MR3%01#3#2R1#4f5R4#<%;131%42p,4segsR1f6R5#9'8f4R6,5231g01R@R2%74g01R`31g01S@R7/:3R8#4%C5P7P31B46f3R7CA,5831%=5g01Sl5121>05g010k513f;R3f:P4P1P3f9f8f7P5P4P6P7f2f1f0M<?C@UUUUUUW4W0W3W5W1W2o"). Qed.

(* [comment removed for export] *)
Definition spinning (c : config) : Prop :=
  to_spin (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.

Lemma spinning_silent_loop : silent_loop spinning.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h06model'i006model'h13ms'i013ms'h22Hhh35modeli025modelh42msi032msh54Hsvch61Hh74Hacch84Hfixh95Hspinh:6Hspin'h;1ci041ch<1oi059cfg_modeli066cfg_msi071mi082m0p;1p;2p;3p;4p;6g02DQR0j1:Tg00?Rj1?Tg00@7j1NTg00@Uj1GTg00?0j1OTg01ZYj16Tg00h\j1=Tg00KVj1MTg01[Oj14Tg011nj17Tg00A8j2FTg00U6j1ETg00]mj32Tg00XJj2<Tg01\Bj23Tg02@HR1j2BTg00<@j31Tg00l8R2j2@Tg02?Ij4LTg00>Uj45Tg01a1j4ATg02EOj6ITg002jj6HTg01]Qj1JTg00^ij4KTg01]7j2CTg00_IR3g00L8R4f1R5f0R6CKp=>f3R7f2R8;15/@6p=01C46p=;1C36p=9%=5=186p=8f4R9A2785;16p=Dg01^RR:P:%:6g00Ln#?#?#?#?#?#?#N#GR:#OR;%65#=%M:R:P;%45#7P:1F34R<#ER=p,4segsR>%47%67321>56,<<R?1356#:R@C0X04#;X13#9C0C0[P6P21385R2#4%62R2'BA8;2:P;1378R2#6#=P:P;%42#7P:P=f5R2/39RA#4RB%6ARC52>P?P@C0X04#;X13#9C0C0P61397RD#4%6DRE'BRFA8;C:RGP1A8;5:A8;8:R1%77=1;:RHP=A2>29RIP?P@C0X04#;X13#9'@'@]2P5%75=1;:P=P>P8P51>85,<<RJDDA8;7:%79=1;:RKP=f6RL=2>2P?P@C0X04#;X13RM#9RN'@P6PKPNP8P3PMP9P4P=PI1>26,<<1326#:C0X04P7A2>97RI1>97,<<51=%:DP5PFA8;E:REP9P7P8P5CLPFeP6PEeC5C5CACAC5C5X21W8W5X34X43P7P8P5P6O4A1=IJ1B78A8;2:%=LRI=1;:f7RJ#7=1;:R1P=f9f8RE52>P?P@C0X04#;X13RF#9RD'@P6P1PDP7P3PFP2P4P=A2>EJ1>L6,<<13L6#:C0X04P9P=P>PJPL1>29,<<DD%:AP81BBCRCPGP5PCeP;PIA1;6:X<;P6%=9P>PJPLP2P9P8EIEHPGeC5C5CACAC5C5W2W:W7X5HX04X13X34X43PLP2P9P7P8P5P6O7n0310710800000024110310200000071103102101100000000000P6O1P;13L2RL#6#=P:P;%4L#7P:P=13EJRE#4%6E52>P?P@C0X04#;X13#9C0C0eW2W9P5P6O2n2001000000121000000X6@X34X43P5P6O2n01104000121106105W;%J0eo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem spin_star_nil : forall ms model tr c',
  to_spin ms model -> m_halted model = None ->
  star segs (mkCfg ms model) tr c' -> tr = [].
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02Hhh15Hspinh25Hstarh32c'h45modelh52msh62trp;1p;2p;3p;4p;7g00;@j1<Tg02@Hj24Tg00?Rj10Tg00@7j15Tg00@Uj1;Tg00?0j1:Tg00h\j11Tg00KVj16Tg00<@j33Tg01\Bj22Tg01oWj47Tg00>Uj48Tg029Jj79Tg00_Ig00L8g01mh#<g01^Rf3R0f2R1'4g00Ln#0#0#0#0#0#0#5#;R2#:R3%10%62R233p,4segsf5R4f4R5'2P0P1C7g02DQf6R6/24P5P0g02F[1464%14=332P1f1C8f0F9W2W0W1W3W6W4W5o"). Qed.

(* [comment removed for export] *)
Theorem spin_obs_iff : forall ms model,
  to_spin ms model -> m_halted model = None ->
  forall tr, obs_trace segs (mkCfg ms model) tr <-> tr = [].
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02Hhh15Hspinh25modelh32msp;2p;1p;3p;4g02@Hj22Tg00?Rj10Tg00@7j15Tg00@Uj14Tg00?0j1:Tg00h\j13Tg00KVj19Tg00<@j31Tg01\Bj26Tg00>Uj47Tg02Gej48Tg00_Ig00L8f1R0f0R1'2g00Ln#0#0#0#0#0#0#5#4R2#:R3%30%92R231g02DQf3R4f2R5'6g02F[1245%35=132P0P1C7C8W0W1W2W3o"). Qed.

(* [comment removed for export] *)
Theorem spin_no_error_run : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02Hhh15Hspinh25modelh32msp;2p;1p;3p;4g02@Hj22Tg00?Rj10Tg00@7j15Tg00@Uj14Tg00?0j1:Tg00h\j13Tg00KVj19Tg00<@j31Tg01\Bj26Tg00>Uj47Tg026Hj48Tg00_Ig00L8f1R0f0R1'2g00Ln#0#0#0#0#0#0#5#4R2#:R3%30%92R231g02DQf3R4f2R5'6g02F[1245%35=132P0P1C7C8W0W1W2W3o"). Qed.

(* [comment removed for export] *)
Theorem spin_no_sstep_error : forall ms model,
  to_spin ms model -> m_halted model = None ->
  forall evs, ~ sstep segs (mkCfg ms model) evs SError.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh12c'h23Heqh34Herrh42Hhh55Hspinh62_Hh73_H0h81ah91eh:3evsh;5modelh<2msi001ci011si021xp;2p;1p;3p;4p;7p;6g02@Hj28Tg00?Rj11Tg00@7j1>Tg00@Uj1<Tg00?0j1ETg00h\j16Tg00KVj1?Tg00<@j30Tg00;@j1=Tg01\Bj25Tg01_Gj4;Tg00>Uj4:Tg021Xj79Tg00;`j1DTg01`;j12Tg02DQR0j13Tg00l8R1j27Tg01]7R2j2CTg0017j6@Tg00=Tj2ATg025oj1BTg01k>R3g01l4R4f0R530p=4g00_Ig00L8f1R6/85g00Ln#1#1#1#1#1#1#>#<R7#ER8%66%?7R730g01mhR9#=R:p,4segsf4R;f3R<'5P5P4C;R=P0f5R0/5;P6P4g02F[180;%6;=087P<f2R7C:P5F9%D9R990:6g01^RR8%25#4%35'7R>X18R?'CR@'7P1A0:79P@g01n^R7P5A0:;9P2P8P?P7P5P1%26#4%36P7P5%2<#4%3;P3P4P3p-0P5P7g01o;n0110100021010000X93g01TL%20P6E@P71A75b0W7W2P6P5O2n2001000000120000000X0>X18P6P5O2n2001000000120102000X0@W6P6P5O2n2001000000120000000b8W3%B=eW:W4W5W;W<o"). Qed.

Theorem spin_no_unmodeled : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02Hhh15Hspinh25modelh32msp;2p;1p;3p;4g02@Hj22Tg00?Rj10Tg00@7j15Tg00@Uj14Tg00?0j1:Tg00h\j13Tg00KVj19Tg00<@j31Tg01\Bj26Tg00>Uj47Tg02Hnj48Tg00_Ig00L8f1R0f0R1'2g00Ln#0#0#0#0#0#0#5#4R2#:R3%30%92R231g02DQf3R4f2R5'6g02F[1245%35=132P0P1C7C8W0W1W2W3o"). Qed.

(* [comment removed for export] *)
Theorem spin_not_all_errors : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ all_traces_error segs (mkCfg ms model).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02Hhh15Hspinh25modelh32msp;2p;1p;3p;4g02@Hj22Tg00?Rj10Tg00@7j15Tg00@Uj14Tg00?0j1:Tg00h\j13Tg00KVj19Tg00<@j31Tg01\Bj26Tg00>Uj47Tg02J<j48Tg00_Ig00L8f1R0f0R1'2g00Ln#0#0#0#0#0#0#5#4R2#:R3%30%92R231g02DQf3R4f2R5'6g02F[1245%35=132P0P1C7C8W0W1W2W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma obs_trace_of_star : forall c0 evs c tr,
  star segs c0 evs c -> is_prefix tr evs -> obs_trace segs c0 tr.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h01ch14Hpreh25Hstarh32c0h43evsh52trh63tr'p;1p;4p;3p;2g00;@j16Tg01oWj41Tg003Hj30Tg00l8j22Tg01]7j25Tg00>Uj44Tg01a1j43Tg01^RR0g01mhR1#6R2p,4segsR3f3R4f2R5f1R6C1A0164P2P3f7P6f0R7C1f4R8=016'2X00,50X62P8P0P3f6f5R9P7C1A0149'2X00P4P3P9P8P4C1A0158P6P7C4C3C3W1W2X52X00W4W3o"). Qed.

(* [comment removed for export] *)
Theorem spin_reach_obs : forall c0 P ms model,
  star segs c0 P (mkCfg ms model) ->
  to_spin ms model -> m_halted model = None ->
  (forall tr, is_prefix tr P -> obs_trace segs c0 tr) /\
  (forall tr c', star segs (mkCfg ms model) tr c' -> P ++ tr = P).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "h02trh12c'h22Hhh34Hpreh45Hspinh55Hstarh65Htailh71Ph82c0h95modelh:2msp;1p;2p;4p;3p;6p;7g00;@j1CTg01\Bj22Tg01oWj43Tg02@Hj25Tg00?Rj10Tg00@7j1<Tg00@Uj1;Tg00?0j18Tg00h\j17Tg00KVj16Tg00<@j31Tg003Hj39Tg028Tj3:Tg008:j34Tg02KLj6BTg00;`j1ATg02LSj2=Tg02M1j7>Tg002jj6?Tg00>Uj4@Tg01^RR0g01mhR1#CR2g00_Ig00L8p,4segsR3f3R4f2R5f1R6f0R7'2C31556g00Ln#0#0#0#0#0#0#<#;R8#8%75%6831f6R89917R9f8R:=:36[^02P3f5,28R3P6P7C3R;A41:5=12:[^10^02P:f7R<P3P6f4R3P7EBX39X02P2%A1f9R9=417=129X021=1:P5P<P8P5P6P3P4P7F>E?X6;X10X02C@W2W4W5W9W:W7W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_self_jump (ms : machine_state) : bool :=
  match ms_svc_pending ms with
  | Some _ => false
  | None =>
    match fetch_word segs (ms_pc ms) with
    | Some w =>
      if is_ecall w then false else
      match decode_any w with
      | Some (Jal rd imm, _) => is_x0 rd && (bv_signed imm =? 0)%Z
      | _ => false
      end
    | None => false
    end
  end.

Lemma is_self_jump_to_spin : forall ms model,
  is_self_jump ms = true -> to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h07Hdecodeh12rdi002rdh23rs1i013rs1h31Hh42opi022oph53rs2i033rs2h63immi043immh72H0h83fmti053fmth96Hecallh:6Hfetchh;4Hsvch<2rmi062rmh=2aqi072aqh>1oi081oh?2rli092rlh@2w0i0:2w0hA4HimmhB1bi0;1bhC3csri0<3csrhD1mhE1nhF5shamti0=5shamthG3sz0hH3Hx0hI1ci0>1chJ3diri0?3dirhK3dsti0@3dsthL1ehM2fmi0A2fmhN1ii0B1ihO5modelhP2mshQ1pi0C1phR4predi0D4predhS3rs3i0E3rs3hT6signedi0F6signedhU3srci0G3srchV4succi0H4succhW2szi0I2szhX4uimmi0J4uimmhY1wi0K1wi0L1xi0M1zp;1p;2p;3p;6p;<p;4p;5p;7g02N4j1pTg011nj1>Tg00?Rj16Tg00?0R0j1DTg00<Zj2@Tg00<@j32Tg0134j1<Tg0141j2:Tg0153j19Tg00A8R1j2JTg0163j13Tg017Pj1=Tg011Ij1ATg00@7j1GTg0188j2;Tg02O6j28Tg02OSj2FTg02@Hj24Tg0017j6XTg00=Tj25Tg00KVj1BTg02P1j2WTg02P]j2VTg00@Uj1ETg016dj2UTg02QIj3TTg00l8R2j2QTg02Qlj2LTg02RLl<KTg02SSj3MTg02T?j4NTg02Tkj5OTg02UWj4PTg02VCj4ITg02Voj4RTg02W[j4STg02XGj3oTg02Y3j4nTg02Y_j4mTg02ZKj5lTg02[7j3kTg00^ij4CTg02[cj4gTg02\Oj4fTg02];j5eTg02]gj6_Tg02^Sj7^Tg02_?j4`Tg02_kj4]Tg02`Wj4aTg02aCj4bTg02aoj7\Tg02b[j6cTg02cGj4dTg02d3j5[Tg02d_j5ZTg02eKj5hTg02f7j5YTg02fcj4iTg02gOj3jTg00Baj2HTg01R@R3f0R4g01SlR532p=1%G4#Ep=7f3R6f2R7f1R8/H432p=?f4R9g01S@R:g010MR;P8P4CC,H7726p=0g00_Ig00L8%p8#1%>7g00LnR<#6R=#6R>#6#6#6R?#6#7R@#DRA1@A4%>6=2A4P0P@f5RB#>=2A4P0P@P3P8g01R`RCP0%7?R?P3p,4segsRDf6RE#<':RFP3P3%94PCP01J:;RGP3%34P1P:P;P3P4P:P3P8PCPC%=8%A=R=#6RH#A#GRI/;4g010kRJ'8'FRKPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCn0110B000S201001042010010420100104301001011044010>1011031045010I10F1001011044010I101103104401021001011044010210010110=40102100101103301001011044010210010110=401021001011035010A10D10H10010130100101104000040102100101103401021001011035010:1071091001016010:1071091001011037010210:1071091001011034010210010110<4010210010J10<40105100101104401051011031047010210510010110310E10660102105100101103106401051001011065010210510010110350102105100101103501021051001011035010@10G1001011064010?10510010130105100101RLn200110C00012010B10MRMPCn10110L00021010C00n0100000020000RNPCn10110L00021010K00n10110L00021010;00#1f7RO/4E]3];P8PA%>EP@P4C?A23C5RPP3PCP3p-0P4g01n^RQg01o;n0110;00020000XL3g01TLP5P4EXR5PQf9RRf8RS'4/54b7W3W;XB@P4O1%>9%B@52AP0P?P3%<B,:DPNPCn10110L00021010K00#1PF%D?RF1@F4%<O,:D=2F4P0P?%<R,:D=2F4P0P?P3P8PNPCn10110L00021010K00#1f;RNf:RA'4R@]3]:P8PF%<A,:DP?P4C?P3P3%98PCP0PGP3%38PMPCn10110L00021010C00n0100000020000#1%97P31@34%96=234P3%9B=234P3P3P8PCP0PGP3%3ERTPMPCn10110L00021010C00n0100000020000#1fARUf@RV'4RW]3]9P8%99RX#1P5PQ15W4b7X3PW9A23XCP0PGP3%3BPMPCn10110L00021010C00#1PT%DGRT1@T4%3O=2T4P0PG%3R=2T4P0PGP3P8PMPCn10110L00021010C00#1fEfDRM'4R0]3]0P8P1P:P;PT%3NPGP4C?P1P:P;P3P8PLn200110C00012010B10M#1fGfFR1'4]3]0P4PTf>RN#3PGP8P4D0P:P3P7PCPCPKPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCPCn0110B000S201001042010010420100104301001011044010>1011031045010I10F1001011044010I101103104401021001011044010210010110=40102100101103301001011044010210010110=401021001011035010A10D10H10010130100101104000040102100101103401021001011035010:1071091001016010:1071091001011037010210:1071091001011034010210010110<4010210010J10<40105100101104401051011031047010210510010110310E10660102105100101103106401051001011065010210510010110350102105100101103501021051001011035010@10G1001011064010?10510010130105100101#1P:PT%3UPGP4P6D0%1LfMRLfLRU'4RC]3]0P6%7=R=%6H#7RHPT%3MRMPG1W84PED0P5PQfQRKfP'4/54b7X3PROW0W6W1P8P4O2PTPMPG1V84PED0POW0X6HX1=P8P4O2%EIPTPMPG1U84PED0%=71;I8/8J'F#1%=6RM1;I7/8JRH;T4%1M%1H'QP2%=9#11;I6/8J#1fRRH/4KP4%=E#11;IE/8J#1P21884#1A2;78[R2A2;841878#1RK[A2;67\K1L84P8n2001000000120000000XD;XE;P2^D;^E;P41;ISRIPJP8O3A2;IJfWRIfVRJPLPAPRf?PHPUfHRRPSP6P4M<KbAb3WAWHP8P4O2n2001000000120000000b3W3W0W6X1=P8P4O2%A<R<#6RL#6#7R2PT%31R1PGAM784PSD0P5PQfS/4H/54b7X3PRHW0W6X2=X1=P7P8P4O3g02h;%AL#7PT%3RRRPGP6P7P8P4CNPAD0P5PQfUfT'4/54b7X3PRKW0W6X5=X2=WIP6P7P8P4O4g02hmRMPTfJ#3ROPGP9P6P7P8P4DOf<RXD0P5PQ14IJ/54b7X3PRJW0X62X2=X1=XT3WGP9P6P7P8P4O5PTPRPGP6P7P8P4CPPAD0PKW0X62X5=X2=XGMP6P7P8P4O4g02iYRMPTPRPGP6P7P8P4CIPAD0PKW0X62X2=X1=W4P6P7P8P4O4%7LPTPRPGP6P7P8P4CRPAD0PKW0WFX2=X1=X4MP6P7P8P4O4PTPRPGP6P7P8P4CSPAD0PKW0X5=X2=X1=X4MP6P7P8P4O4PTP1PGAo784PSD0PHW0X62X2=X1=P7P8P4O3PTPRPGP6P7P8P4CnPAD0PKW0XF=X2=X1=X4MP6P7P8P4O4PTPRPGP6P7P8P4CmPAD0PKW0X5=X2=X1=X4MP6P7P8P4O4%7>R>PTPOPGP9P6P7P8P4DlPXD0PJW0X2=X1=XV>XR>WMP9P6P7P8P4O5PTP1PGAk784PSD0PHW0X62X2=X1=P7P8P4O3PT%3VR>PGP:P;g02jEP7CCC?P5PQ15C4b7X3PRCW0PTP>PGP:P;g02k1P7CCC?PCW0g02k]RCPTPRPGP6P7P8P4CgPAD0PKW0X5=X2=X1=W4P6P7P8P4O4PTPRPGP6P7P8P4CfPAD0PKW0X5=X2=X1=X4CP6P7P8P4O4g02lIRCPTPOPGP9P6P7P8P4DePXD0PJW0X2=X1=X?3X=3W@P9P6P7P8P4O5PT%3URUPGPBP9P6P7P8P4E_PND0P5PQfYfX'4/54b7X3PR>W0X5=X2=X1=X?3X=3X@CPBP9P6P7P8P4O6g02m6PTfN#3RMPGPEPBP9P6P7P8P4F^PVD0P5PQf[fZ'4/54b7X3PRLW0X5=X2=X1=X?3X=3X@CW4PEPBP9P6P7P8P4O7g02mbRCPTPRPGP6P7P8P4C`PAD0PKW0XC2X2=X1=W4P6P7P8P4O4PTPRPGP6P7P8P4C]PAD0PKW0XC2XX=X1=X4CP6P7P8P4O4g02nNRCPTPRPGP6P7P8P4CaPAD0PKW0X62X2=X1=W8P6P7P8P4O4PTPRPGP6P7P8P4CbPAD0PKW0X62X5=X2=X8CP6P7P8P4O4g02o9%7<R<PTPMPGPEPBP9P6P7P8P4F\PVD0PLW0W<XS=X5=X2=X1=X8CW4PEPBP9P6P7P8P4O7g02oePTPUPGPBP9P6P7P8P4EcPND0P>W0X<<X5=X2=X1=X8CW4PBP9P6P7P8P4O6PTPRPGP6P7P8P4CdPAD0PKW0X<<X2=X1=X8CP6P7P8P4O4g030RPTPOPGP9P6P7P8P4D[PXD0PJW0X5=X2=X1=X8CW4P9P6P7P8P4O5g031?PTPOPGP9P6P7P8P4DZPXD0PJW0X5=X2=X1=X8CW4P9P6P7P8P4O5g031oPTPOPGP9P6P7P8P4DhPXD0PJW0X5=X2=X1=X8CW4P9P6P7P8P4O5g032\RBPTPOPGP9P6P7P8P4DYPXD0PJW0X<<X2=X1=XUBWKP9P6P7P8P4O5g033JPTPRPGP6P7P8P4CiPAD0PKW0X2=X1=X8CWJP6P7P8P4O4PTP1PGAj784PSD0PHW0X2=X1=X8CP7P8P4O3n0110B000S201001042010010421100104301001011044010>1011031045010I10F1001011044010I101103104401021001011044010210010110=40102100101103301001011044010210010110=401021001011035010A10D10H10010130100101104000040102100101103401021001011035010K1071091001016010K1071091001011037010210K1071091001011034010210010110<4010210010J10<40105100101104401051011031047010210510010110310E10660102105100101103106401051001011065010210510010110350102105100101103501021051001011035010@10G1001011064010?10510010130105100101P8P4O2W3W0XW;XN:P8P4O2n200110C00012110B10MXQGP4O1%3S%BG52TP5PQ1504b7X3PW0n10110800021110C00P4P7O2b0b>W3W9n0110;00020001P4P7O2b9bBW3W:XY?P4O1%<S,:D%B?52FP5PQ15@4b7X3PW:n10110800021110;00P4P7O2b:b>W3W;n10110800021010;01P4P7O2b;b>W3WOWPo"). Qed.

(* [comment removed for export] *)
Fixpoint spin_c (fuel : nat) (ms : machine_state) (model : Model) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if is_self_jump ms then true
    else
      match ms_svc_pending ms with
      | Some _ => false
      | None =>
        match mi_account_step segs ms model with
        | MachineOk (ms', model') => spin_c fuel' ms' model'
        | _ => false
        end
      end
  end.

Lemma spin_c_to_spin : forall fuel ms model,
  spin_c fuel ms model = true -> to_spin ms model.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP1"; "WithSegs"] "p'0h01Hh14Hacch22Hjh34Hsvch42H0h54fuelh65modelh72msh81bi001bh92IHh:1eh;1mi011mh<6model'i026model'h=3ms'i033ms'h>1oi041oh?6resulti056resulti061pi071xp;3p;2p;6p;1p;4p;7g0347j32Tg02@Hj24Tg0017j6=Tg00=Tj29Tg0353j1GTg02N4j17Tg00<Zj28Tg00<@j30Tg00?Rj16Tg00@7j1<Tg00@Uj1;Tg011nj15Tg00A8R0j2ITg00]mj33Tg035Rj3HTg00?0R1j1FTg00Baj2ETg00KVj1CTg00U6R2j1ATg00XJj2:Tg00^ij4BTg02AGj7@Tg00[]j1?Tg00\ej1DTg036\j4>Tg01R@R3f0R4g01SlR530p=1g00MSR6g00_IR7g00L8R8f2R9f1R:;24#1149:[]6]7R;X56g037=?2:4#1P3g01R`R<P3p-0P4g01n^R=g01o;n0110000020000X:3g01TLP5P4E=R>P=f3R?/49/94b4W0X68X77%G??2:4#1%79P31834%7?=034P3f5R@#7=034P3P3P:P5P1g00Ln#6#6#6#6#6#6#<#;RAP3f6RB#5RCP<P21I78RDP3p,4segsRE?3B@P0P7P8P3P4f;RF?2:4n2001105000120103102P<P<n1011070003101050000n10110700021010000n0100000020000#1f7RG/4B]0]2P:f4RH#7RI#1A0355AHB@:W0W2A03I<P1PAP3%5@P<P2PDP3A3E@HP0P7P8P3P4f:RH?2:4n2001105000120103102P<P<n1011070003101050000n10110700021010000#1PC%FARC18C4%5G=0C4P1PAf9RG#5=0C4P1PAP3P:P<P2PDP3A3EHGR1P0P7P8P3P4f?R@?2:4n2001105000120103102P<P<n1011070003101050000n10110700021010000#114FH]0]3P:%5H1EA450CA03<5R5P>P=f=RIf<RB'4/94b4W0W3X8AP4O1f8RJ#5%CA50CP2PDP3A3EGJP0P7P8P3P4f>RJ?2:4n2001105000120103102P<P<n1011070003101050000#1P1%ADR11814A3EFH=014P2PDA3EIB=014P2PDP3P:P0P7P8P3P4fCR2?2:4n2001105000120103102P<P<n1011070003101050000#114@JR<]0]1P:P0P7P8A3E@J1:D4501P0P7P8P3P:fDR3?2:4n2001105000120103102#1fAR0f@'4]0]1P4fB=3E0P7P8P:P4CB,:D501fER0?29:#1P3P2P?P9PFP:P0P?P9P4O3F@W0W1X<8X=7P:P4O2n2001106000120101101X?DP4O1A3EBFRB%?D501P>P=19<4b4X05R5W1%DD901BP5W1n1011010003101050000P4P9O2b1b;W0W3n10110400021010001P4P9O2b3b>W0W2n0110000020001P4P9O2b2b8W0X68X77X9;X56P4C>W5o"). Qed.

End WithSegs.

(* [comment removed for export] *)
End WithFP1.
Ltac prove_to_spin fuel :=
  apply (spin_c_to_spin _ fuel);
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section TwoBranchToy.
Variable segs : list Segment.
Variable c0 : config.
Variable evs_g : list event.
Variable c_g c_r : config.
Variable T : list event.
Variable P : config -> Prop.

Hypothesis Hsplit : forall evs to, sstep segs c0 evs to ->
  (evs = evs_g /\ to = SNext c_g) \/ (evs = [] /\ to = SNext c_r).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.

Theorem spin_branch_toy_obs_iff : forall tr,
  obs_trace segs c0 tr <-> is_prefix tr (evs_g ++ T).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP2"; "TwoBranchToy"] "p'0h01Hh14Hpreh25Hstarh33tr2h45Hsteph51ci001ch62c2h73evsh83tr'h95Htailh:2trh;1oh<3Heqh=5Hobs2h>4cendh?5HpreTh@2_HhA1ehB4tr''i011si021xp;1p;3p;4p;5p;2p;6p;8p;9g00;@j1UTg028Tj3;Tg01oWj41Tg037\j5STg00;`j1RTg01`;j14Tg01_Gj45Tg00<@j32Tg01]7R0j26Tg020JR1j2MTg02:Tj3LTg006Dj2TTg002jj6Hj8Al9KTg002Mj6GTg005Ij2ETg00>Uj4CTg01a1j4BTg038[j5DTg007>j6JTg029Jj8QTg0017j6PTg039cj4OTg03:>j8NTg008:j3FTg003Hj3ITg00l8R2j2?Tg01mhR3f1R4f0R53Fp=3AI345p=0f2R6AI345'?p=@g01^RR7/65p=9f4R8f3R9P6P4C1/?5p==A2745p=8A2964/?5p=:f5R:P8P9P6P4C1/?5'?p=<AF3459296p=>g01k>R;?245p=7%U3R<p,4segsR=p,2c0R>;;5R?p,5evs_gR@p,1TRA'3RB,04[105BRCA;=>4[P0P<P=P>P4P5C1RD?@94X57#9X8<106BP5A@D:4X57#9P0P7P=P>P6P5f6RE/06D=X5710EBP5P=P>P8P5f8RF/08D=P2P=P>P:P4C1f9RG/0:f:RH/0BP5P=P>f7RIP9C1f<RJ/0FP=P>PGP:P4DSP<PG%R3RK18:>C:P=P>P6%44RLC5RMP=P4P5PF1365RN92<JE<X3<,6<X67#9X7<,6<'MP1P<PHPK18E>C:PMP=P4P5PGf=RO=2<NE<X3<,6<X67#9X7<,6<f?RP/0BP5P<f;RQPK18I>C:P2A2<JK18F>fARR/0BRSP5f>RT=2<KP<PKP=P>P5PJC1fERU/0418T>fGRV/0B[]1]2X8<P=P>PKPQC1fDRW/0K18O>fFRX=L34A2<XKRYP<PKPCX:<RZ1T3BR[PVP5EHb1W@W1W2PPP5PIPEGAW0P4P5O2n2001000000120000000W0P5O1PMP=P4P5PHA2<TNE<X3<,6<X67#9X7<,6<P0P<PMP=P4P5PQA2<PNE<X3<,6<X67#9X7<PSP5PMP=P4P5POA2<RNE<X3<,6<X67#9P0P7P=P>P9PLC5P=P4P5PTP<fBRNP9P5C>E<X3<,6<X6710UBP5P=P>P:PLC5P=P4P5f@RLP<PWP:P5C>E<X3<,6<P0P<P=P>PE%46C5P=P6P5PRP<PUPEP5C>E<X3<fIRM/0BP5P=P>PF%48C5P=P8P5fCRSP<PVPFP5C>E<P2P=P>PG%4:C5P=P:P4PWP<fHR\PGP4C>D=fMR]/0BP5P=P>PQ%4IC5P=PFP8PVP<fKR^PJP8C>D=P2P=PGP:P\C1P<fLRJPOP:C>fQ/0BP5P=PQPIfJR_C1P<fOPLPFC>P<13RGR`P=P>P5P]C1fVR]/04fW/0B]1]2X8<P=P>P`PJC1fUR`13NH'0p,6HsplitPS%4PRaPIO3P<PSP@p,3c_gRb#4Rc,7aC:P<PSPKp,3c_rRd#4Re,7aC:'MP1P<PWP@%4LR1/7cC:P<PWPK171eC:fX/0BP5P<PUP@%4RR1/7cC:P2A2<X@%4NRX/7cfZ/0BRWP5A2<\@P<P@f]135N'0RaP=P>134SP]C1R]P=P>P6%4\RSC5Rf%4MRg/7cfa/0BRh[]4]2]1X7<f\Ri13@R'0P=P>13@NP`C1P=P>P@%4VRjC517ScP;P7P;P7P5P5P_n0110100021010000XA;RkPgPcP5EG18Mb18_bP7PbP=P>P@%45RlC5P=P4PMPiC1feRm/0B]9Rn]4X67P=P>P@PcC5P=PbP\f[RcC1P<P=PbP4P5C1Ro?@^4X57#9X8<PMP7P=PbP_P510__D=X57PiP=PbPMPiC110MMP51E3MCCCBCBA;=bMP2A;=b5104A[Rp105AA;=b4Rq[106A\qp,6Hg_obsRqP5O1P4n2001000000120000000X:<Pp^:<P5P^P4O210^AP3fg13@JPBPHP3P@PJPAP5DDEJb=b0b=W9W4P^P5P9PPGAW0P5O1b0W<W4W2W1PMP5PEPIPOM9KW0P4P5O2n2001000000121000000W0P5O1P<PUPK171eC:P2PY17XePWP5A2<\KP<PK17gePh[^4f^2]^1aX7<13KR,0iP=P>13KNP`C1P=P>PKPjC517SeP;P7PkPgPeP5EG18Md18_dP7PdP=P>PKPlC5Pn]4X67P=P>PKPeC5P=PdP\PcC1P<PM13K5,0mX3<PIPKP=p,1PPdPMPip,5Hloopp,4HP_rP5GQEPfd13KK'0AL3m5A2<mKP<PKPZP[ffP5EHb1b1W9W4P^P5P9PPGAW0P5O1b0W<W4W2W1PMP5PEPIPOM9KW0P4P5O2n2001000000121000000W0P5O1n200100000021100011000b;W1W2fPP5P\PVGAW0W9P4P5O2n2001000000121000000W0W4P4P5O2n2001000000121000000W0X3<P4P5O2n2001000000121102000W0X67P4P5O2n2001000000121102000W0X7<P4P5O2n2001000000121102000W0P5O1n200100000021000011000b;W1W2P4P5O2n2001000000121000000W0X>7P4P5O2n2001000000121102000W0X8<P4P5O2n2001000000121102000X0?A;=bAR?10AARV[P?\VPqPAO11E3ACOA@oA4X57#9RoX8<Rq,6<P0P<PqA;=>9P5P0P7P=PbP6P510A6D=X57A;=>IP5P=PbP8P510A8D=P2P=PbP:P4C110A:A;=>QP5P=PbPIP9C110AFP<A@DL4X57#9X8<13@GRLP7P=P>13@HRHP510PHD=X57P:P=P>PLP:C110TLP=P>P@PbPGP:p,7Hstep_gP4GNP3PTPBPLPOP3P@PAPGP5DDEJCCCBCBW?W2P4P5O2n2001000000120000000W0X>7P4P5O2n2001000000120102000X0oXB<P4P5O2n2001000000120102000b;X1CCCW:o"). Qed.

Theorem spin_branch_toy_no_error : ~ reaches_error segs c0.
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) ["WithFP2"; "TwoBranchToy"] "p'0h01Hh13evsh23tr2h32c2h42_Hh51ci001ch63Heqh75Hsteph85Htailh92trh:4Herrh;5Hstarh<1oh=4cerrh>1eh?4evs1i011si021xp;2p;1p;4p;5p;3p;8p;6g0255j2LTg00;@j1KTg01]7R0j21Tg01oWj45Tg037\j5FTg00;`j1ETg00<@j30Tg00l8R1j22Tg01`;j13Tg01_Gj46Tg020JR2j2?Tg00=Tj2ITg002jj8>Tg002Mj6ATg00>Uj4@Tg01a1j4=Tg026Hj6GTg025oj1HTg008:j3BTg0017j6DTf2R3f1R4f0R5g01l4R6C6p=9f4R7f3R8P3P4C5/25p=4g01^RR9/15p=;A0945p=8g01mhR:?B45p=Jf5R;P7P8P3P4C5/25'2p=:g01k>R<P6P3g01TLP4P5EDp=CAB:459083p=<A0<45p=7p,4segsR=p,2c0R>'LR?P0%K:R@P=P>P3P4A9=45RAD4X1@,1@X59#;RBX9@g01n^RCP5P0P9P=P>P8P4PAD4X1@,1@X59PCP5P=P>P;P4PAD4X1@,1@P0P@P=P>f6RDP3A9=35D4X1@PCP5P=P>f8REP7A9=75D4P1P=P>f9RFP;C5A9=;4PCP5P=P>f;RGf7RHC5A9=E7P=P>f=RIPFP4DF%E:R:90@I18F>'2P=P>P3%34RJC6RKP=P4P5f<RLf@RM1J35RN50@E:X2@,1@X39#;X1@,1@'?P2f>RO=0@:RPf:RQ/8>'2PKP=P4P5PIfARR=0@NE:X2@,1@X39#;X1@,1@PCP5f?RS=0@:RT18G>'2P1A0@M:RU18L>PCP5fBRV=0@:RW18S>P9P>P=P>fERXP5C5A9=4OPC]:];X=9P=P>fDRYP>C5A9=>Ip,6HsplitRZPOP6P5O3p,5evs_gR[90@Op,3c_gR\#3R]90<6R^'2p,3c_rR_#3R`90<6R6,2P'?P2A0@S[/2^12T6PCP5A0@M[/2^P1A0@R[RTP^PCP5fCRP=0@[RaP<p-0P5PCg01o;n0110100021010000X><Rb?C]5PC1IC5Rcb0X6^W4P4P5O2n2001000000120000000W0P5O112U6P1A0@R:RUP6PCP5A0@P:R^ACb`5PCPcb0X66W4P4P5O2n2001000000120000000W0P5O1n200100000021000010000b<W:W;PMP5PEPHG>W0W4P4P5O2n2001000000120000000W0P5O1PKP=P4P5POA0@VNE:X2@,1@X39#;X1@,1@P0P@PKP=P4P5PSA0@PNE:X2@,1@X39#;X1@PCP5PKP=P4P5PRA0@XNE:X2@,1@X39#;P0P9P=P>P8PJC6P=P4P5PVP@fFRNP8P5C<E:X2@,1@X39PCP5P=P>P;PJC6P=P4P5PYP@fHRJP;P5C<E:X2@,1@P0P@P=P>PD%33C6P=P3P5PXP@fIPDP5C<E:X2@PCP5P=P>PE%37C6P=P7P5fGP@fKRDPEP5C<E:P1P=P>PF%3;C6P=P;P4PJP@fLRJPFP4C<D4PCP5P=P>PG%3HC6P=PEP7PDP@fOPLP7C<D4P1P=PFP;PJC5P@fPPIP;C<PCP5P=PGPHfNC5P@fSPMPEC<PZPR%3IRIP;O317I],2T17I`,2U'?P2A0@V[%3ORV/7]'217V`,2WPCP5%3SRS/7],2aP1A0@Y[%3MRM/7]PCP5A0@N[%3PR[/7]P<P9P<P9P5P5PXn0110100021010000X><Ra%3YRWP]P5EA18Y\18X\P9P\P=P>PD%35C6P=P4PYf[RDC5PC]8]7X39RVP=P>fJR2P]C6P=P\PPfZR]C5p,8Hg_noerrP@P=P\P3P4PAD4X1@,1@X59#;X9@PYP9P=P\PNP4PAD4X1@,1@X59PDP@P=P\PXf\RUA9=U5RID4X1@fWRTP=P\PYPDC5A9=DTR\P5fRR;C@C=C=C=O1W8W7PNP5POPQG>W0P5O1b0W6W4P4P5O2n2001000000120000000W0P5O117S`,2^P1A0@Y:17M`PCP5A0@N:17[`P<P9PaPWP`P5EA18Y_18X_P9P_PVP=P>P2P`C6P=P_PPP]C5P=p,1PP_p,5Hloopp,4HP_rP@P=P_P3P4PAD4X1@,1@X59#;X9@PYP9P=P_PNP4PAD4X1@,1@X59PDP@P=P_PXPUPID4X1@PTP=P_PYPDC5P\P5P;C@C=C=C=EGW8W7PNP5POPQG>W0P5O1b0W6W4P4P5O2n2001000000120000000W0P5O1n200100000021000010000b<W4W8P4P5O2n2001000000121000000W0W7P4P5O2n2001000000121000000W0X2@P4P5O2n2001000000121102000W0X39P4P5O2n2001000000121102000W0X?@P4P5O2n2001000000121102000W0P5O1n200100000021100011000b<W:W;P4P5O2n2001000000121000000W0X1@P4P5O2n2001000000121102000W0X=9P4P5O2n2001000000121102000X0BX9@P4P5O2n2001000000121102000W0%H?eo"). Qed.

End TwoBranchToy.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithFP2.
Module SelfJumpImage.

Definition spin_seg : Segment := {|
  seg_base := 0x10000;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["6f000000"%pstring]
|}.
Definition spin_segs : list Segment := [spin_seg].
Definition spin_img : Image :=
  mkImage spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6).

Example j_dot_decodes :
  decode_any (Z_to_bv 32 0x6f) = Some (Jal 0 (Z_to_bv 21 0), 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) [] "p;2p;1p;3p;4p;6g00A8j2CTg00?0j1BTg00?Rj10Tg00@7j12Tg011Ij11Tg01A:j13Tg00m=j25Tg0163j1:Tg01AXj39Tg016dj27Tg00^ij46Tg00Baj28Tg00<@j34j1ATg03;1j4@Tg03;Oj2?Tg03;lj6<Tg00<Zj2=Tg03<Dj2>Tg03<bj3;Tg01S@R0g010MR1'CR2#BR3g00LnR4#0R5#0R6#0#0#0#2%14#0#1#1#1#1#3'5#:R4P0P1%15R5#2g010kR7g01TL39%05#1#2/57'7%36C6,82R634R7P3P3%A3P0g03=JP1g03>;C@,?2P4P6E<R6g01R@R4g01SlR2'=1>76=442d3;o"). Qed.

Lemma spin_img_to_spin : forall sp brk0 mbase (rnd : EntryDraw) lim inp,
  to_spin spin_segs
    (init_machine_state spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6) sp rnd
       (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    (init_model (segments_reserved spin_segs) brk0 mbase sp lim inp).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) [] "h04brk0h13inph23limh35mbaseh43rndh52spp;1p;3p;9p;6p;2p;=g00?Rj10Tg00@7j13Tg00@Uj1:Tg011Ij12Tg03>Tj3PTg03?Tj1LTg03@Jj1FTg03A@j1DTg03B5j1CTg03Bll9BTg03Ckj1@Tg03Dij6?Tg01A:j1>Tg00m=j2=Tg01AXj3QTg00?0j1<Tg00KVj1OTg00<Zj2;Tg0134j1KTg0141j2ITg00Baj2HTg00<@j36j19Tg03Ebj1ETg03;Oj2GTg03;lj65Tg03<Dj27Tg03<bj38Tg0153j1JTg017Pj1ATg0188j2MTg02RLl=NTf0R0#0#0p=1g01R@R1g01SlR2760p=4g00LnR3#0R4#0R5#0#1R6#0R7#3#:R8g03FJg010MR9g03GJg03HDR:P:%07#1R7#0#1#1#1#3%27#1#1#1#3%23R3#2#0#1#3%03R3#33Pf5R7f2%L0%F0%D0%C0M9BR;%@:f4f3P7f1P0E?%36R6%23#2#2#2#>'=R3%24R4#3g010kR0g01TL3QR7%04#2#3R4/=0R<%>5%<8%O8';%:6R5#<R=%K;,I:R:1H53R;36R>P=P=%9=%E6,G5P:P;E5R;1;12R:17>;#4d38%J3R3g01R`R;561R>P1P1%91R5g03IQR6P3P;E5R;P:17>;#4d38g03Io%A7R7#4R;P1P1P5P6P7P2E5R2P:17;2#4d381M4<R<=690R4P9P9%99g03>;P<P0E5R0P:1740#4d38M=NW1W2W4X38X08W5o"). Qed.

Example spin_img_obs_iff : forall lim en inp tr,
  bh_traces (run spin_img lim en inp) tr <-> tr = [].
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) [] "p'0h03inph12trh24brk0h32enh43limh55mbaseh63rndh72spi001ei016en_brki027en_drawi03<en_mmap_basei045en_spp;1p;4p;2p;3p;9p;6g00;@j1JTg03K@j46Tg03L0j25Tg00;`j17Tg00<@j3ITg03Lfj24Tg00@7j12Tg00@Uj1:Tg00?Rj11Tg011Ij13Tg03>Tj38Tg03?Tj19Tg03@Jj1HTg03A@j1GTg03B5j1CTg03Bll9@Tg03Ckj1?Tg03Dij6>Tg03M?j6=Tg00?0j1ATg00KVj1BTg00<Zj2<Tg03NSj6;Tg03OUl9DTg028Tj3ETg03PMj4FTf0R0#1#1p=0g010Mg03QER1P1g03GJR1g01mhR2#JR3g03R=R4f4R5f2R6f1R7C6/50%729I30R2'4]1]0P0g00LnR8#0#0#0R9#2#:R:g03FJg03HDR;P;%19#0R9#1#0#0#0#2R<%39#0#0#0#2%38R8#3#1#0#2%18#238R8f5R9P6%97%H7%G7%C7M9@%?;P5f3R=P9f;R>P7E>P9P5P=P6P>P7E=%A:%B:'<P0E;P;P<P8P9P5P=P6P>P7M9D=E;0/42eP4P>P9P5P=P6CFP7C6/50/42eX13X01W6X5:X2:W7P=P6P7P0O4n01100000141104101103102W3W4o"). Qed.

Example spin_img_no_error : forall lim en inp,
  ~ bh_errors (run spin_img lim en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) [] "p'0h03inph14brk0h22enh33limh45mbaseh53rndh62spi001ei016en_brki027en_drawi03<en_mmap_basei045en_spp;4p;1p;3p;9p;6p;2p;5g03K@j45Tg03SIj16Tg025oj13Tg00@7j12Tg00@Uj1DTg00?Rj11Tg011Ij14Tg03>Tj3;Tg03?Tj1:Tg03@Jj17Tg03A@j18Tg03B5j19Tg03Bll9GTg03Ckj1FTg03Dij6ETg03M?j6CTg00?0j1BTg00KVj1?Tg00<Zj2>Tg03T?j5@Tg03OUl9ATg0255j2=Tg03PMj4<Tf0R0#1#1p=0g010Mg03QER1P1g03GJR1g03R=R2f3R3f1R4P0C5#6#3]0P0g00LnR5#0#0#0R6#2#DR7g03FJg03HDR8P8%16#0R6#1#0#0#0#2R9%46#0#0#0#2%45R5#4#1#0#2%15#23;R5f4R6P4%:0%70%80%90M9G%F8P3f2R:P6f:R;P0EEP6P3P:P4P;P0EC%B7%?7'>D@P8P9P5P6P3P:P4P;P0M9A,=8#3eP2P;P6P3P:P4C<P0C5#6#3eX01W5X47X17W6P3P:P4P0O4n01100000141104101103102W2W3o"). Qed.

Example spin_img_not_all_errors : forall lim en inp,
  ~ bh_all_errors (run spin_img lim en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) [] "p'0h03inph14brk0h22enh33limh45mbaseh53rndh62spi001ei016en_brki027en_drawi03<en_mmap_basei045en_spp;4p;1p;3p;9p;6p;2p;5g03K@j45Tg03UFj16Tg025oj13Tg00@7j12Tg00@Uj1DTg00?Rj11Tg011Ij14Tg03>Tj3;Tg03?Tj1:Tg03@Jj17Tg03A@j18Tg03B5j19Tg03Bll9GTg03Ckj1FTg03Dij6ETg03M?j6CTg00?0j1BTg00KVj1?Tg00<Zj2>Tg03V@j5@Tg03OUl9ATg02<Uj2=Tg03PMj4<Tf0R0#1#1p=0g010Mg03QER1P1g03GJR1g03R=R2f3R3f1R4P0C5#6#3]0P0g00LnR5#0#0#0R6#2#DR7g03FJg03HDR8P8%16#0R6#1#0#0#0#2R9%46#0#0#0#2%45R5#4#1#0#2%15#23;R5f4R6P4%:0%70%80%90M9G%F8P3f2R:P6f:R;P0EEP6P3P:P4P;P0EC%B7%?7'>D@P8P9P5P6P3P:P4P;P0M9A,=8#3eP2P;P6P3P:P4C<P0C5#6#3eX01W5X47X17W6P3P:P4P0O4n01100000141104101103102W2W3o"). Qed.

(* [comment removed for export] *)
Example spin_img_to_spin_by_execution :
  to_spin spin_segs
    (init_machine_state spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6)
       (Z_to_bv 64 65536) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0))
       [[]] [] (Z_to_bv 64 1000) hwcap_rv64gc)
    (init_model (segments_reserved spin_segs) (Z_to_bv 64 1048576)
       (Z_to_bv 64 0x7fff7f800000) (Z_to_bv 64 65536) 0x40000000%Z
       (mkProcInput [[]] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
          net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48)).
Proof.
ltac2:(KReplay.run1 (kr_t_DivergeSim ()) [] "p;1p;3p;2p;9p;6p;4p;5p;=g0353j1LTg00?Rj10Tg00@7j16Tg011Ij15Tg03>Tj3CTg01A:j17Tg00m=j24Tg00@Uj1:Tg03WIj2<Tg00;@j1;Tg00;`j18Tg00=4j3KTg03Bll9JTg03Ckj1ITg00A8j2HTg03Dij6BTg0347j4ATg00<@j39j1@Tg03;lj6?Tg00<Zj2DTg03<Dj2>Tg03<bj3FTg03XIj5GTg03YMl==Tf0R0#0#0p=3%00#0#0#0p=1%50#5p=2f6f5f4g03ZGf3f2f1g03[Cg03\<P0g03]9R0g01R`g03^:M==p=Eg03HDR1g037=#LR2P1g00LnR3#0#3R4#0#3R5#0R6#3R7#0#3#1R8#6%57#3#1#6%53R3#5R7#0#3#6%03#63C%65R5%78'4R3%66g010kR6'4%:5R9%64R4/46U'<%:4R4#;R:%84%8:R43KR;P4%27R7#0#5#0R<#3#7,45R=P0M9JR0%I1%18R8#7,45%27#2#2#2#2#0#2#2#2#2#0#3#1#1#1#1#1#7,45P3%38#1#1#7P;P4g0000/H:#8P=%5<#0#7,45%891456FEEBR6g01R@R5P1P2P0P6CAR6g01SlR039R2P5P5%@5g03IQP6P0E?R61D501>26=950d3FDGo"). Qed.

End SelfJumpImage.
