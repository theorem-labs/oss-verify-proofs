(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import ShapeAlg PureModel RefNodesMF StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_13084_14000 RCode_15000_16000.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import StartupBase StartupDefs Startup1 Memset304 Startup2 Startup3 Startup3b Startup4.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Startup () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01I59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg9rz_mstepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:StartupTac3bwdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powi69OSSVerify5KrLib6Common4Musl7Startup:main_entry00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc7rl_segsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib6Common9CliDriver3Amb<mkProcInputCC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8with_tidC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidK59OSSVerify5KrLib6Common9PureModel7md_pure01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common9PureModel7md_pure00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7Startup6bwd_rzC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC69OSSVerify5KrLib6Common9CliDriver3Amb6a_drawC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib6Common8MemSplit4cmemC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb5a_uidC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver3Amb7a_hwcapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit9wfJ_constC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup16p1_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup19regs_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup12J1C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ArgvEnv8envp_ptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC46Stdlib5Lists4List2InI47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K4ELinuxProcessSemantics5Riscv5Instr5instr02K69OSSVerify5KrLib6Common5Reloc:RelocSites6sshape01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common5Reloc:RelocSites5csite01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:RelocSites6cs_blkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:RelocSites5cs_opC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:RelocSites7cs_addrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc:RelocSites4rl_wC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib6Common5Reloc:CanonSites9rl_site_FC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl7MuslTac>rl_ret_ok_nearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic6eq_symC46Stdlib6ZArith4ZdivBZminus_mod_idemp_lC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ArgvEnv5argcNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit:wfJ_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit3wfJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit6win_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Common8MemSplitAstore_ok_cmem_winC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl9Memset304=memset304_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ZStores5zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib6Common4Musl;StartupDefs6envp_wC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C35stdpp7tactics<f_equal_helpI47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Common8PropExec5v_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs5J_lsmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs5J_auxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs4pn_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs6D_libcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5RelocARCode_15000_160007F_156f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc5Reloc;rl_addi_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesMF@md_pure_with_tidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModel9mp_haltedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9PureModel7mp_lazyC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC59OSSVerify5KrLib6Common8GresFast?getr_upds_foundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs6argc_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs3rwaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4v_lwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs3rwbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs8canary_wC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7Startup6J_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs6D_mainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs6argv_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs8aux_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl;StartupDefs5rnd_wC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01k69OSSVerify5KrLib6Common4Musl7Startup:main_entry01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup46fin_c9C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup46fin_c8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup46fin_c7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup46fin_c6C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl9Startup3b6tls_c5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:RefNodesMF=rz_set_tid_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl9Startup3b6tls_c4C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup36tls_c3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup36tls_c2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup36tls_c1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl8Startup26p3_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7ZStores<length_zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit?wbytes_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit9cmem_initC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC59OSSVerify5KrLib6Common8PropExec9init_mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec8wrap_memC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Common8GresFast5rlookC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8GresFast>getr_upds_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3fx0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib6Common4Musl:RelocStart4RPH0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib6Common7CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C69OSSVerify5KrLib6Common4Musl9Memset304;memset_clobC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00c69OSSVerify5KrLib6Common4Musl7Startup3HloC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7Startup3HhiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl7Startup3HalC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K69OSSVerify5KrLib6Common5Reloc:RelocSites3sop01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common5Reloc:RelocSites5skind01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc:RelocSites5csite00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K46Stdlib9micromega=RingMicromega3Op201C69OSSVerify5KrLib6Common5RelocARCode_15000_160007W_156f8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5RelocARCode_15000_160007E_156f8C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC69OSSVerify5KrLib6Common9CliDriver3Amb6amb_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_stdinc69OSSVerify5KrLib6Common4Musl7Startup?ref_startup_secC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c69OSSVerify5KrLib6Common4Musl7Startup6me_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit>rdn_cmem_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=cmem_at_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib6Common8MemSplit6in_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit;cmem_at_winC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib6Common8MemSplit<cmem_at_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8MemSplit=rdn_cmem_dataC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := rl_segs.
Abbreviation RPH := RPH0.
(* [comment removed for export] *)
Local Notation rsegs := rl_segs (only parsing).
Local Notation rph := RPH0 (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["VP1"] "h02sth12Hhh25Hlazyh33Hmsh44Hst'h51Kh65modelh74segsh83st'p;1p;3p;2p;9p10000p4p7210p1000\p4p710p8g001:j11Tg001Zj10Tg002?j1:Tg002]j15Tg003@j1?Tg003bj1<Tg004Yj1;Tg005;j32Tg005Uj29Tg0065j16Tg006mj17Tg007Mj38Tg008Hj23Tg009=j34Tg00:<l9>Tg00;:j2=Tg00<4#1g00=3g00=ig00>b#0#0#0#0#0#0#:#5R0#?f1R1#<%;0321900R0#1f2R2#6%7032g00?GR0f6R3f0R4781f7R51313f5R634f8f3R7P2P5P3P6f4R3P1P4M9>W4W3X80W01343=467X00,=3eW2W1W5W6W7o"). Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (rl dF_15170 0x15280) (pn_w sp0 av ev) s1v (rl dA_2f848 0x2f868)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (rl dF_15170 0x15288)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (rl dF_15448 0x1547c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (rl dF_1539c 0x153cc)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (rl dA_1e348 0x1e350)).
End GD_1.    (* [comment removed for export] *)

(* [comment removed for export] *)
Section GD_2.
  Context {RL : Reloc}.
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = rl dF_15448 0x1548c;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = rl dA_2f6b0 0x2f7b8;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = rl dF_131d0 0x131d0;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.
End GD_2.

Section Assembly.
  Context {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
  Context {AMB : Amb}.
  #[local] Existing Instance fx0.   (* [comment removed for export] *)
  Variable sp : word.
  Variables argv envp : list (list byte).
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Assembly"] "h01Hh12_Hh21vp;1p;2p;3g002?j1:Tg00@Nj28Tg00A8j24Tg00ATj17Tg00B2j2;Tg005;j39Tg00BRR0j25Tg00Bmj13Tg001Zj12Tf0R1#2#2#2#2p=0%21#2p=6%31#3p=1p,4Hvspg00CRg00>bR2#0R3#6#:p,2sp'8R4'4R5g00DM,44g00EH%73,;4g00Ef39'5R3'5P0P5P3%32#1#1#1#1#1#1#1#2#6#0#0#0#0#0#0#0#7/44P1f1R4X13X05P4P1O2n2001000000120000000b2o"). Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Assembly"] "h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g002?j17Tg00@Nj25Tg00A8j22Tg00ATj14Tg00B2j28Tg005;j36Tg00BRR0j23Tg001Zj10Tf0R1#0#0#0#0p=:%01#0p=9%01#0#0#0#0#0#0#0p=1p,4Hvspg00CRg00>b#:R2#9R3#7p,2sp'5R4'2R5g00DM,24R6g00EH%42,84g00Ef36R2'3R7'3P0P5P7%03#1#1#1#1#1#4,24R4P1P0P6P2P4P1f1R4X32X06P4P1O2n2001000000120000000X17X25P4P1O2n2001000000121000000b4o"). Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Assembly"] "h01Hh12H0h22_Hh33_H0h41vp;1p;2p;3g001Zj10Tg002?j17Tg00@Nj23Tg00A8j21Tg00ATj16Tg00B2j25Tg005;j34Tg00BRR0j22Tp,4Hvspg00CRg00>b#0#0#0#0R1#0#0#7p,2sp'3R2'1R3g00DM,12R4g00EH%61,52g00Ef34R2'2R1'2P0P3P1P2f0R5P0P4P2P2P5P5X02X34f1R4P5O2n2001000000120000000X11X23P4P5O2n2001000000120000000b4o"). Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  (* [comment removed for export] *)
  Variable rpc : N.
  Hypothesis Hrpc : Z_to_bv 64 (Z.of_N rpc) = rl dF_13084 0x13084.

  Theorem ref_startup_sec : forall brk mbase lim fs0 stdin0 K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp argv envp tid regs mem ->
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (rl dF_131d0 0x131d0) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
    pose proof (u64_range sp) as Hsp.
    unfold init_config. cbn [cfg_ms cfg_model in_argv in_envp in_uid in_hwcap].
    set (model := init_model (segments_reserved rsegs) brk mbase sp lim (mkProcInputC argv envp fs0 stdin0)).
    assert (Hh : m_halted model = None) by reflexivity.
    assert (Hlazy : m_vm_lazy model = []) by reflexivity.
    assert (Ht0 : m_tid model = None) by reflexivity.
    assert (Hpure : md_pure model) by (constructor; reflexivity).
    set (RZ := fun st : machine_state => realizes rsegs (mkCfg st model) K).
    assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
    rewrite init_mkst.
    rewrite Hrpc.
    rewrite cmem_init. fold (regs_init sp).
    destruct (p1_run sp argv envp a_uid a_hwcap a_draw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
      as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R1 |].
    pose proof A1 as A1'.
    destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp a_uid a_hwcap a_draw) (J1 sp argv J0) (fun _ => None))
                (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (rl dF_15170 0x1519c) A1')
      as [regs2 [mem2 (R2 & M2 & G2)]].
    { rl_ret_ok. }
    { exact A10. } { exact A11. } { exact A12. }
    { rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
      replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
      symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
    { rewrite u_Z2bv by lia. lia. }
    { apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
    rewrite wbytes_cmem_win by region_side.
    carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
    carry G2 A3 (3:reg) B3.
    change (realizes SEGS (mkCfg ?st model) K) with (RZ st).
    eapply (p3_run sp argv envp a_uid a_hwcap a_draw) with (G := RZ); try side Hva Hve HG.
    { unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
    intros regs3 C1 C2 C10 C18 G3.
    carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
    assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
    { intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
        clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
        repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
    pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
    pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
    pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
    pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
    pose proof (Cz 27 ltac:(in_list)) as Z27.
    change (J1 sp argv J0) with (J_lsm sp argv J0).
    eapply (tls_c1 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4a; intros.
    eapply (tls_c2 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4b; intros.
    eapply (tls_c3 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4c; intros.
    eapply (tls_c4 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ) (tid := Z_to_bv 64 0); try side Hva Hve HG.
    intros regs4; intros.
    unfold RZ at 1.
    eapply (rz_set_tid_at SEGS regs4 (rl dF_15490 0x156ec) _ (seg_rom SEGS) model W_156ec K Hpure F_156ec E_156ec);
      [ match goal with H : getr regs4 17 = _ |- _ => rewrite H; reflexivity end | exact Ht0 |].
    intros tid Htid. change Fork.PID_MAX_ENVELOPE with (2^22)%Z in Htid.
    replace (v_addi (rl dF_15490 0x156ec) 4) with (rl dF_15490 0x156f0) by (symmetry; exact (rl_addi_lit _ _ _ _ eq_refl)).
    set (model' := with_tid tid model).
    assert (Hpure' : md_pure model') by (apply md_pure_with_tid; exact Hpure).
    pose proof (mp_halted _ Hpure') as Hh'. pose proof (mp_lazy _ Hpure') as Hlazy'.
    set (RZ' := fun st : machine_state => realizes rsegs (mkCfg st model') K).
    assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
    change (realizes SEGS (mkCfg ?st model') K) with (RZ' st).
    eapply (tls_c5 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs5; intros.
    eapply (fin_c6 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs6; intros.
    eapply (fin_c7 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs7; intros.
    eapply (fin_c8 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs8; intros.
    eapply (fin_c9 sp J0 argv envp a_uid a_hwcap a_draw) with (G := RZ'); try side Hva Hve HG'.
    intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
    unfold RZ'. apply (HK tid regs9). { exact Htid. }
    split; try assumption.
    - intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
    - eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
      + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
      + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
  Qed.

End Assembly.

(* [comment removed for export] *)
Section Summary.
  Context {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLI : RelocImg RL} {RLD : RelocData RL} {RLW : RelocRW RL RLD} {RST : RelocStart RL RLD}.
Theorem ref_startup : forall (rpc : N), Z_to_bv 64 (Z.of_N rpc) = rl dF_13084 0x13084 ->
  forall sp brk mbase draw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry RL (amb_of inp draw) sp (in_argv inp) (in_envp inp) tid regs mem ->
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (rl dF_131d0 0x131d0) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Summary"] "h02HKh14Hrpch23Hsph33Hvah43Hveh51Kh63brkh74drawh83inph93limh:5mbaseh;3memh<4regsh=3rpch>2sph?3tidp;1p;2p;3p;8p;5p;6p;Gg001Zj11Tg002?j15Tg002]j1<Tg00VMj1STg00Tlj2QTg00Bmj10Tg00IAj2;Tg00ATj13Tg00caj28Tg005;j3>Tg02a2j1=Tg00Vkj17Tg02agj1RTg00Waj16Tg02b^j1PTg0000j2LTg003@j1KTg00@Nj2FTg00FDj2:Tg00F`j2ETg00BRj2DTg02cUj29Tg00G=j8CTg00HBj1BTg00JAj1GTg02@3j5HTg00K=j1ATg00MAj6ITg00N:j2JTg008Hj2@Tg009=j3?Tg02dUj1MTg02eIj1NTg02f@lGOTf0R0#1#1p=2%00#1p=4g02[ig00>bR1#1R2#1R3#1R4#1#2#5R5#<R6%S0,Q5p,2RLR7%01#0#0#4#0R1#1#2';%03#4#2R3#1#0#2#2#0#2#3'83>g02gHg00EHg02hHg00=if6R8#=f2R9#7#Rf3R:#6#P%02R;#5/L6%54#<#K\6g00Ef1F59R5':%32%4;#3'E,:5'DP7f8R5f:R;'9f=R2%75%65P:P9f1R4GC%B7R<g02GPP:%01#2,;7%03#0#4#0#2#2#3'8P9%G<DHf4R3%A<P2f<R2f>P;f9R<EI'J'@;?5[[];]<^?6P7p,3RLCp,3RLSp,3RLIp,3RLDp,3RLWp,3RSTf5R7f7'9P;%77%67P9P4P:P2f;P<P5P8%M7%N7P3P0MGOW0W4W3W2W5W8W9W7X:6X66X>6W1W=o"). Qed.
End Summary.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {RL : Reloc} {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62Hnh72_Hh81ah91eh:3memh;1nh<4segsi001xp;1p;2p;9p;6p;3p;7p;4p;8g001:j19Tg001Zj14Tg002?j1<Tg002]j1:Tg00@Nj27Tg00A8j2?Tg01IUj1ETg019:j2CTg00ATj1;Tg00F`j2ATg02iBl9@Tg003@j18Tg01Gbj25Tg01hJj66Tg005;j30Tg00\^j1JTg00]]j1ITg00ZCj1HTg02@lj7GTg01iIj7DTg00[ej43Tg00BRR0j22Tg00gKR1j2=Tg02jAj41Tg00G=j8>Tg02k9l9BTg000\j7FTg00<4#9g00>b#4R2#4#4R3#4#4#4R4#<R5#:R6g02NMp,3sp0R7,75f1R8,75'?f2R9,75%E8'C%;2%;4'A'?p,2RLR4p,3AMBR2P7p,2avR5p,2evR:p,3tidR;p,4regsR<p,3memR=p,2MER>M9@%<3#:R3#8\6R?1578P4P2P7P5P:f0R@E6RA90?8P7g02HdP7P5P:%J2%I2RB%H2RCFGRDP8P4P7P5P:PBPCP;FDRCC390?='2'2X16,=6RBX2?RE'=P1P?PE%93#8R3f6REP=f5RFf4RGC1PEPDPFPGC130P@P1P61579A0?9AP7PDP9PCC390?='2'2X16f:R9P=f9R1f8REC1P9PDP1PEC1503P@157GA0?GAP7PDPGPCC390?='2'2P0157FP4P2P7P5P:P8E690?FP7PDPFPCC390?='2f>RAP=f=R9f<RHC1PAPDP9PHC1503P@f7RI,57P4P2P7P5P:PGE690?EP7PDPEPCC390?='2P0P4P2P7P5P:PFE690?1P7PDP1PCC390?=fBR1P=fARFf@R0C1P1PDPFP0C1503P@f;P4P2P7P5P:PIE650?P7PDPHPCC390?=P?P7PDP9PCC3R9P4P2P7P5P:P;P<P@G>fGRHP8fFRIfER0C1PHPDPIP0C1503]3X:?P4P2P7P5P:P;P<P9G>P7PDPIPAPCP0fDfCP1M9BW3P=P@P>FFW0W7P8P@O2n2001000000121000000W0W4P8P@O2n2001000000121000000W0X16P8P@O2n2001000000121100000X0BX2?P8P@O2n2001000000121100000b9W6W5W;W8W<o"). Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw a.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;9p;6p;3p;7p;4p;8g001Zj13Tg002?j1;Tg002]j18Tg00@Nj27Tg00A8j2ETg02iBl9@Tg003@j1?Tg01Gbj25Tg01hJj64Tg005;j30Tg00\^j1>Tg00]]j1=Tg00ZCj1<Tg02@lj7Dj86Tg01iIj7CTg00[ej41Tg00BRR0j22Tg00gKR1j29Tg00G=j8:Tg02l<j6ATg000\j7BTg00>b#3#3#3R2#3#3#3#;R3#8R4p,3sp0R5,73f0R6,73'Ep,2RLR3p,3AMBR7P5p,2avR8p,2evR9p,3tidR:p,4regsR;p,3memR<p,2MER=M9@%;2#8#?R2\4R>f1R?,55P3P7P5P8P9P6E4R@90>?P5g02HdRAP5P8P9%>7RB%=7RC%<7RDFDREP?P3P5P8P9PCPDP:FCRFC190><'2'2X14,94RGX2>RH'9P1P>PHP<f3RHO1PAP5P8P9PBPCPDPHG6502P6P1P4f2R1,55A0>1@P5PEP1PFC190><'2'2X14P<f7R1O1PAP5P8P9PBPCPDP1G6502P6f4RH,55A0>H@P5PEPHPFC190><'2'2P0f5R@,55P3P7P5P8P9P?E490>@P5PEP@PFC190><'2P<f;RIO1PAP5P8P9PBPCPDPIG6502P61551f8RJP3P7P5P8P9PHE450>P5PEPJPFC190><'2P0f9R0P3P7P5P8P9P@E450>P5PEP0PFC190><P<f?R0O1PAP5P8P9PBPCPDP0G6502P6P3P7P5P8P9P1E490>IP5PEf<PFC190><P>P5PEf=PFC1RIP3P7P5P8P9P:P;P6G:P?fDR1O1PAP5P8P9PBPCPDP1G6502]3X9>P3P7P5P8P9P:P;PIG:P5PEf>PFfCfBEAW3P<P6P=FBW0W6P?P6O2n2001000000121000000W0W4P?P6O2n2001000000121000000W0X14P?P6O2n2001000000121100000X0GX2>P?P6O2n2001000000121100000b8W5W7o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh44__x1h54__x2h64__x3h72HJh82Hah92_Hh:7__arithh;4__ffh<8__varmaph=5__with>1ah?1eh@3memhA1oi001xp;1p;2p;9p;6p;3p;7p;4p;8p;5g001Zj13Tg002?j1CTg002]j1>Tg00@Nj2:Tg00fWj2;Tg00A8j29Tg00FDj28Tg00BRR0j21Tg02iBl9LTg003@j1GTg01Gbj25Tg01hJj66Tg005;j30Tg00\^j1^Tg00]]j1VTg00ZCj1UTg02@lj7RTg01iIj7QTg00[ej42j5[Tg00gKR1j2@Tg004Yj1ATg018Dj14Tg00G=j8?Tg006mj1NTg001:j1MTg01<1j2=Tg01T2j4KTg01<Oj1ITg01<mj1HTg01=Xj27Tg01>^j3JTg00Bmj1FTg01BCj4<Tg02m>j7ETg02BMj8OTg01?Aj2PTg00Ooj2DTg01?cj2STg01@Oj3TTg01@nj4]Tg02mbj2\Tg02n]j6WTg000\j6Xj7YTg02Aij7ZTf1R2g02JKR3g02JjR4P4g02KJR5f0R6g02KjFZp=Bg00>bR7#3R8#3#3R9#3#3#3#CR:#>R;p,3sp0R<,::R=g02LJR>';1::6R?'918?='1p,2RLR?p,3AMBR@P<p,2avRAp,2evRBp,3tidRCp,4regsRDp,3memREp,2MERFM9L%C9#>R9#GRG\;RH15<2P?P@P<PAPBP6E6RI90H2P<g02HdP<PAPB%^@%V@RJ%U@RKFRRLP2P?P<PAPBPJPKPCFQRKC290HE'1'1X1;,@;RJX2HRM'@P1PHPMPEf3RMO1%A9R950G#4P6P1P;f2R1,5<A0H1IP<PLP1PKC290HE'1'1X1;PEf7RNO1=0G9#4P6f4RO,5<A0HOIP<PLPOPKC290HE'1'1P0f5RI,5<P?P@P<PAPBP2E690HIP<PLPIPKC290HE'1PEf;RPO1=0G9#4P615<Nf8RQP?P@P<PAPBPOE650HP<PLPQPKC290HE'1P0f9R0P?P@P<PAPBPIE650HP<PLP0PKC290HEPEf?O1=0G9#4P6P?P@P<PAPBPNE690HPP<PLf<PKC290HEPHP<PLf=PKC2RPP?P@P<PAPBPCPDP6G?P2fDRNO1=0G9#4]3X@HP?P@P<PAPBPCPDPPG?PGf>RPfCRDO1A0G69#4XAGf6PDg00EHRGg02Y2R9#N%M9PG1=G1P21=GMCK%IG%HGR9P3P4P4P5P9P3P4P4P5PG17G7R317G85JGg02Id%F7,7GR7C<,B9PGP7g02Z^P3C<,B9FER3%A4P3GO1P95P6P1g02Y^R9g02Z>R5'D1S61=095dg00Ef=TG2C]b;b<b=X4GX5GW61;62/911816'11;21/9M18M2'1[^4G^5G^6GP61::NP>P=PDO4b:1\<DeR=O2P<PLPPPKPDD[P<PLPPPKPDP=EWEXW3PEP6PFFYW0W9P2P6O2n2001000000121000000W0W7P2P6O2n2001000000121000000W0X1;P2P6O2n2001000000121100000X0JX2HP2P6O2n2001000000121100000b?W8W>o"). Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Consumers"] "p'0h01Hh14__x1h24__x2h34__x3h43s1vh51Jh62MEh77__arithh84__ffh98__varmaph:5__with;4cstrh<2HJh=3Hhih>3Hloh?2_Hh@1ahA1ehB3memhC1nhD4segsi001xp;1p;2p;9p;6p;3p;7p;4p;8p;:g001:j1FTg001Zj15Tg002?j1ATg002]j1@Tg00@Nj29Tg00fWj2=Tg00A8j23Tg01IUj1<Tg019:j2:Tg02iBl9OTg003@j1JTg01Gbj27Tg01hJj66Tg005;j30Tg00\^j1]Tg00]]j1VTg00ZCj1UTg02@lj7TTg01iIj7RTg00[ej42Tg00BRR0j21Tg00gKR1j2CTg02o]j48Tg00G=j8BTg01Roj1QTg006mj1PTg01<1j2?Tg01T2j4NTg01<Oj1LTg01<mj1KTg01=Xj2;Tg01>^j3ITg00Bmj1MTg01BCj4>Tg004Yj1HTg01?Aj2GTg00Ooj2STg01?cj2`Tg01@Oj3_Tg01@nj4^Tg01HZj1\Tg02C1j3WTg01LFl:XTg000\j7YTg02Aij7ZTg02BMj8[Tg02Y^R2f0R3g02Z>R430p=4f1R5g02JKR6g02JjR7P7g02KJR8P3g02KjFZp=Ef3R9P6P7P7P8f2R6P5P3G[p=Dg00<4#Fg00>bR:#5R;#5#5R<#5#5#5#AR=#@R>g02NMp,3sp0R?,9=R@g02LJRA'=19=5'319=6%<5':/3@p,2RLRBp,3AMBRCP?p,2avRDp,2evREp,3tidRFp,4regsRGp,3memRHp,2MERIM9O%A<#@#J\>R<17?5PBPCP?PDPEP3E6RJ90<5P?g02HdP?PDPE%]C%VCRK%UCRLFTRMP5PBP?PDPEPKPLPFFRRLC290<H'1'1X4>,C>RKX5<RN'CP1P<PNf6RNPHf5ROf4RPC8#4P3P1P>17?6A0<6JP?PMP6PLC290<H'1'1X4>f:PHf9R1f8RQC8#4P317?PA0<PJP?PMPPPLC290<H'1'1P017?OPBPCP?PDPEP5E690<OP?PMPOPLC290<H'1f>RJPHf=RRf<RSC8#4P3f7RT,7?PBPCP?PDPEPPE690<QP?PMPQPLC290<H'1P0PBPCP?PDPEPOE690<1P?PMP1PLC290<HfBPHfAf@C8#4P3f;PBPCP?PDPEPTE650<P?PMPSPLC290<HP<P?PMPRPLC2RRPBPCP?PDPEPFPGP3GBfGRSP5fFRTfER1C8#4]6XB<PBPCP?PDPEPFPGPRGBP?PMPTPJPLP1fDRLPN%QLRNg00EfRJ%<L'3RMg00EHRRg02Y2RG#PRF%FGRGPR1?R6P51?R9CNRE%LRRD%KRRCPR1;R:RB1;R;R;5IRg02IdRO%M:,;RR:C>,ECR0%H7R7P0CD1GC8R8P3P61S241`36#4dA_RJ5C^RJb8b9b:X1RX2RW31=35/361=56/39[^1R^2R^3RP319=SRSPAP@P1O4b7b;%\?19=1'3ePNPMPFPGPEPDPCPRAWRB;POP:C>,ECRCP7PCCDP8PJb8b9b:X1RX2RX3R1:35/361:56/39[^1R^2R^3RP3P@%<TPSPLO4b7b;M:XW6PHP3PIFYW0W?P5P3O2n2001000000121000000W0W<P5P3O2n2001000000121000000W0X4>P5P3O2n2001000000121100000X0KX5<P5P3O2n2001000000121100000bAW=W>WCW@WDo"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev a_hwcap a_draw tid a.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memi001xp;1p;2p;9p;6p;3p;7p;4p;8g001Zj13Tg002?j1<Tg002]j18Tg00@Nj27Tg00fWj2GTg00FDj29Tg02iBl9ATg003@j1@Tg01Gbj25Tg01hJj64Tg005;j30Tg00\^j1>Tg00]]j1=Tg00ZCj1FTg02@lj7ETg01iIj7Dj86Tg00[ej41Tg00BRR0j22Tg00gKR1j2:Tg00G=j8;Tg01HZj1BTg030]j6?Tg000\j7CTg00>b#3#3#3R2#3#3#3#<R3#8R4f0R5,73p,3sp0R6,73g02LJ'G'9p,2RLR7p,3AMBR8P6p,2avR9p,2evR:p,3tidR;p,4regsR<p,3memR=p,2MER>M9A%<2#8#@R2\4R?f1R@,56P7P8P6P9P:P5E4RA90?@P6g02HdP6P9P:%>8%=8RB%F8RCFERDP@P7P6P9P:PBPCP;FDREC190?='2'2X14,:4RFX2?RG':P1P?PGP=f3RGO1P7P6P9P:PBPCP;PGG6502P5P1P4f2R1,56A0?1AP6PDP1PEC190?='2'2X14P=f7R1O1P7P6P9P:PBPCP;P1G6502P5f4RG,56A0?GAP6PDPGPEC190?='2'2P0f5RA,56P7P8P6P9P:P@E490?AP6PDPAPEC190?='2P=f;RHO1P7P6P9P:PBPCP;PHG6502P51561f8RIP7P8P6P9P:PGE450?P6PDPIPEC190?='2P0f9R0P7P8P6P9P:PAE450?P6PDP0PEC190?=P=f?R0O1P7P6P9P:PBPCP;P0G6502P5P7P8P6P9P:P1E490?HP6PDf<PEC190?=P?P6PDf=PEC1RHP7P8P6P9P:P;P<P5G;P@fDR1O1P7P6P9P:PBPCP;P1G6502]3X9?P7P8P6P9P:P;P<PHG;P6PDf>PEfCREfB173E%B6'9eE?W3P=P5P>FCW0W6P@P5O2n2001000000121000000W0W4P@P5O2n2001000000121000000W0X14P@P5O2n2001000000121100000X0FX2?P@P5O2n2001000000121100000b8W5W7o"). Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev a_hwcap a_draw tid) a n.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup ()) ["Consumers"] "p'0h01Hh13s1vh21Jh32MEh42HJh52Hah62_Hh71ah81eh93memh:1nh;4segsi001xp;1p;2p;9p;6p;3p;7p;4p;8g001:j1@Tg001Zj14Tg002?j1:Tg002]j19Tg00@Nj27Tg01IUj1?Tg019:j2<Tg00fWj2DTg00A8j2=Tg02iBl9ATg003@j18Tg01Gbj25Tg01hJj66Tg005;j30Tg00\^j1JTg00]]j1ITg00ZCj1HTg02@lj7GTg01iIj7ETg00[ej42Tg00BRR0j23Tg00gKR1j2;Tg02jAj41Tg00G=j8>Tg01HZj1CTg031^j8BTg000\j7FTg00<4#@g00>b#4#4#4R2#4#4#4#:R3#9R4g02NMf1R5,73f0R6#?'<p,3sp0R7,73g02LJ'D'=p,2RLR8p,3AMBR9P7p,2avR:p,2evR;p,3tidR<p,4regsR=p,3memR>p,2MER?M9A%:2#9R2#8\4R@1575P8P9P7P:P;P6E6RA90@5P7g02HdP7P:P;%J9%I9RB%H9RCFGRDP5P8P7P:P;PBPCP<FERCC290@>'3'3X14,;4RBX2@RE';P1P@PE%@2#8R2f5REP>f4RFf3RGC1PEPCPFPGC130P6P1P4f2R1,57A0@1AP7PDP1PCC290@>'3'3X14f9R1P>f8RGf7RHC1P1PCPGPHC1502P6157FA0@FAP7PDPFPCC290@>'3'3P0157EP8P9P7P:P;P5E690@EP7PDPEPCC290@>'3f=RAP>f<RIf;RJC1PAPCPIPJC1502P6157HP8P9P7P:P;PFE690@GP7PDPGPCC290@>'3P0P8P9P7P:P;PEE690@1P7PDP1PCC290@>fAR1P>f@REf?R0C1P1PCPEP0C1502P6P8P9P7P:P;PHE690@JP7PDPIPCC290@>P@P7PDPAPCC2RAP8P9P7P:P;P<P=P6G>fFRIP5fERJfDRHC1PIPCPJPHC1502]3X9@P8P9P7P:P;P<P=PAG>P7PDPJf>PCPHfCRCfB173H%?C'<%C7'=eGBW3P>P6P?FFW0W6P5P6O2n2001000000121000000W0W4P5P6O2n2001000000121000000W0X14P5P6O2n2001000000121100000X0BX2@P5P6O2n2001000000121100000b8W5W:W7W;o"). Qed.
End Consumers.
