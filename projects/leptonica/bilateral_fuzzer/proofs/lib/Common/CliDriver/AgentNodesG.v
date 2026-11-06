(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import AgentLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AgentNodesG () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib6Common8PropExec:step_ecallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG5ependC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib6Common8PropExec7getr_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib6Common8PropExec9arg_reg_0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common8PropExec9arg_reg_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec9arg_reg_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG9arg_reg_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG9arg_reg_4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG9arg_reg_5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib6Common7CatExec7adv_setC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7FileSim;adv_eff_retC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG=adv_set_ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC59OSSVerify5KrLib6Common6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG@step_ecall_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic3and01C59OSSVerify5KrLib6Common6CatSim6fdchanC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idc69OSSVerify5KrLib6Common9CliDriver;AgentNodesG=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib6Common8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7CatExecAms_read_bytes_rdnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG=ms_gpr_epend2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG=ms_gpr_epend1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib6Common8ShapeAlg;rz_write_chC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes4bool02C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions?bv_and_unsignedC59OSSVerify5KrLib6Common7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib6Common8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG@bv_and_255_smallC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG6rz_sysC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver;AgentNodesG:rz_exit_atC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.

Section G.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;  (* [comment removed for export] *)
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03memh12pch24regsh33romh44segsh51wp;1p;2p;3p;9p;5g0000R0p4p7210p1000\p4p710p8g001:j1DTg001Zj10Tg002?j14Tg002dj11Tg003Bj13TP0j2<Tg003ej15Tg004Gj28Tg005Ij27Tg005kj32Tg006Ej16Tg007El99Tg008Dj1:Tg009Lj5CTg00:Ej2BTg00;Aj1ATg00;_j2=Tg00<Bj3>Tg00<ej2?Tg00=^j5;Tg00>ej2@Tg00?m#Dg00@l#0R0#4#1R1%00#0R0#0#0R2#0#1#3R3'<%10#3#5\3R4%12#3R2%52f5R5f3R6'8f0R7,7232g00AQf1R2#6g00B132p,2fxR8f7R9f6R:P5f4R;P6f2P2P7M99g00BQR7#:P8P:P5P;P6DC,B9P:P5P;P6%40#AR0g00CX1=10d5>1,?:D;,@732eUUW5X34W0X13W2W4o"). Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j17Tg002dj11Tg003Bj12Tg0000j26Tg003ej13Tg005Ij25Tg00D4j24Tg00@l#0R0#7#1%00#0R0#0#0#0#1#2R1'6%10#2#3\1R0%31f0,51'4X41X30W0X11W2o"). Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j1ITg002dj16Tg003Bj12Tg0000j2HTg003ej1CTg00;Aj1<Tg00<Bj35Tg00DNj27Tg00<ej24Tg005kj30Tg00E8j21Tg00Ebj38Tg00FFj6GTg00Fbj2FTg00GAj1ETg00GZj3BTg00HVj4=Tg00I2j1>Tg00IRj2?Tg00Ioj2@Tg000\j6ATg00=^j5;Tg00JUj1:Tg00KTj2DTg00;_j29Tg00@l#3R0#IR1#6R2%30#3R0#3#3#3#6#2R3'H%60#2#C\3R0%22R4%31#<R1g00CXR5552R6f5R7f0R8'71476503X54P3f4R7/46R91776g00LRR:=525R;9046R4g00M0R<%28R=f1R>#2R?g00MNf2R@#2?0>8g00MiRAf3RB/1@11B>30[RC11@>11@850A%2B?0@>RD[117B117@50A\DA8@>8P>n2001000000120000000W3W2W4PC^3?^2=^4<P8P2P6P;P>O41126112;50APAP1PAp-0P8g00NGR;g00NdP;n011000003001000010000X6AP5P:P8EGP;1F;8b0b1b0W1%E4e9B76C=g00O@R6#>,?1,@2R4g00O_EAP7PBP@P>P8D;R8#:/74=039e1D86P51921d9521,47503eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j19Tg002dj17Tg003Bj13Tg0000j2JTg003ej1DTg00;Aj18Tg00<Bj35Tg00DNj24Tg00<ej26Tg005kj30Tg00E8j21Tg00Ebj3:Tg00FFj6ITg00Fbj2HTg00GAj1GTg00GZj3CTg00HVj4BTg00P]j1?Tg00I2j1>Tg00IRj2@Tg00Ioj2ATg000\j6=Tg00=^j5<Tg00JUj1ETg00KTj2;Tg00;_j2FTg00@l#2R0#9R1#7R2%20#2R0#2#2#2#7#3R3'J%70#3#D\3R0%32R4%91#8R5g00CXR6552R7f5R8f0R9'41687503X54P3f4R8/67R:1487g00LRR;=526R<9047R4g00M0R=%39R>f1R?#3R@g00MNf2RA#3?0?9g00MiRBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA:A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P2P7P<P?O41127112<50BPBP5PBp-0P9g00NGR<g00NdP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G4e9C87CB%21#8g00O@#?R1#>'@,A2R7g00Q<E=P8PCPAP?P9D<R9#E/47=03:e1;91P61F25d9525,68503eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j1:Tg002dj17Tg003Bj13Tg0000j2JTg003ej1DTg00;Aj19Tg00<Bj35Tg00DNj24Tg00<ej26Tg005kj30Tg00E8j22Tg00Ebj3;Tg00FFj6ITg00Fbj2HTg00GAj1GTg00GZj3CTg00HVj4BTg00P]j18Tg00I2j1?Tg00IRj2@Tg00Ioj2ATg000\j6>Tg00=^j5=Tg00JUj1ETg00KTj2<Tg00;_j2FTg00@lR0#1R1#:R2#7R3%11#1R1#1#1#1#7#3R4'J%71#3#D\4R1%33R5%:0#1#1#9R0g00CXR6553R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00LRR;=536R<9057R5g00M0R=%39R>f1R?#3R@g00MNf2RA#3?0?9g00MiRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NGR<g00NdP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#9g00O@#8#8R2#?'@,A3R7g00R:E>P8PCPAP?P9D=R9#E/47=04:e1<92P61F30d9530,68504eX;4X:1W7X84W9o"). Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00E8j20Tg00Ebj37Tg001Zj15Tg002?j14Tg002dj1<Tg00;Aj16Tg00P]j13Tg00I2j1;Tg00IRj28Tg00Ioj29Tg00<Bj3:Tg00D4j2=Tg00M0R0f0R1#1R2f1R3#1R4g00MNf2R5#1?231g00MiR6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@lR1#5#4R0#<R2%50#6g00O@#3#3#3#;'8,92%41#5#4#6g00CX5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00E8j20Tg00Ebj37Tg001Zj15Tg002?j14Tg002dj1<Tg00;Aj16Tg00P]j13Tg00I2j1;Tg00IRj28Tg00Ioj29Tg00<Bj3:Tg00D4j2=Tg00M0R0f0R1#1R2f1R3#1R4g00MNf2R5#1?231g00MiR6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@lR1#5#4R0#<R2%50#6g00O@#3#3#3#3#;'8,92%41#4#5#6g00CX5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj10Tg005kj33Tg00E8j22Tg00Ebj37Tg001Zj16Tg002?j14Tg002dj1<Tg00;Aj15Tg00P]j11Tg00I2j1;Tg00IRj28Tg00Ioj29Tg00<Bj3:Tg00D4j2=Tg00M0R0f0R1#0R2f1R3#0R4g00MNf2R5#0?331g00MiR6f3R7/25127333R8[12531251536%07?353[R9f4#0?375\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@lR1#6#4R0#<R2%60#5g00O@#1#1#1#1#1#;'8,92%41#4#4#5g00CX5:2R11221,=6O4b3o"). Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j19Tg002dj15Tg003Bj13Tg0000j2JTg003ej1DTg00;Aj1:Tg00<Bj38Tg00DNj24Tg00<ej26Tg005kj30Tg00E8j22Tg00Ebj3;Tg00FFj6ITg00Fbj2HTg00GAj1GTg00GZj3CTg00HVj4BTg00P]j17Tg00I2j1?Tg00IRj2@Tg00Ioj2ATg000\j6>Tg00=^j5=Tg00JUj1ETg00KTj2<Tg00;_j2FTg00@lR0#1R1#9R2#5R3%11#1R1#1#1#1#5#3R4'J%51#3#D\4R1%33R5%90#1#9#:R0g00CXR6583R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00LRR;=836R<9057R5g00M0R=%39R>f1R?#3R@g00MNf2RA#3?0?9g00MiRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NGR<g00NdP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#:g00O@#7#7#7R2#?'@,A3R7g00S8E>P8PCPAP?P9D=R9#E/47=04:e1<92P61F30d9830,68504eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j19Tg002dj15Tg003Bj13Tg0000j2JTg003ej1DTg00;Aj1:Tg00<Bj38Tg00DNj26Tg00<ej27Tg005kj30Tg00E8j22Tg00Ebj3;Tg00FFj6ITg00Fbj2HTg00GAj1GTg00GZj3CTg00HVj4BTg00P]j14Tg00I2j1?Tg00IRj2@Tg00Ioj2ATg000\j6>Tg00=^j5=Tg00JUj1ETg00KTj2<Tg00;_j2FTg00@lR0#1R1#9R2#5R3%11#1R1#1#1#1#5#3R4'J%51#3#D\4R1%33R5%90#9#1#:R0g00CXR6583R7f5R8f0R9'61787504X55P4f4R8/77R:1687g00LRR;=836R<9057R5g00M0R=%39R>f1R?#3R@g00MNf2RA#3?0?9g00MiRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NGR<g00NdP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#:g00O@#4#4#4#4R2#?'@,A3R7g00TCE>P8PCPAP?P9D=R9#E/67=04:e1<92P61F30d9830,78504eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j15Tg002dj16Tg003Bj12Tg0000j2JTg003ej1DTg00;Aj1:Tg00<Bj38Tg00DNj29Tg00<ej27Tg005kj30Tg00E8j21Tg00Ebj3;Tg00FFj6ITg00Fbj2HTg00GAj1GTg00GZj3CTg00HVj4BTg00P]j14Tg00I2j1?Tg00IRj2@Tg00Ioj2ATg000\j6>Tg00=^j5=Tg00JUj1ETg00KTj2<Tg00;_j2FTg00@lR0#3R1#5R2#6R3%31#3R1#3#3#3#6#2R4'J%61#2#D\4R1%23R5%50#5#5#:R0g00CXR6583R7f5R8f0R9'91787504X55P4f4R8/77R:1987g00LRR;=836R<9057R5g00M0R=%29R>f1R?#2R@g00MNf2RA#2?0?9g00MiRBf3RC/1A11C?30[RD11A?11A950B%2C?0A?RE[118C118A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41137113<50BPBP0PBp-0P9g00NGR<g00NdP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%32#:g00O@#4#4#4#4#4R2#?'@,A3R7g00UNE>P8PCPAP?P9D=R9#E/97=04:e1<92P61F30d9830,78504eX;4X:1W7X84W9o"). Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h04addrh13memh22pch34regsh44segsh52x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00VYj24Tg00D4j25Tg00?m#8g00@l#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1P0^01f4f1'4'5X51W1X21W3W4o"). Qed.

Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
  ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h04addrh13memh22pch34regsh43romh54segsh62x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00WPj24Tg00D4j25Tg00?m#8g00@l#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1R2P0^01f5f2'4'5X61X42W1X21W3W5o"). Qed.

Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00D4j23Tg00@l#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f2,30X41X30W0X11W2o"). Qed.

Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00D4j23Tg00@l#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f1,30X41X30W0X11W2o"). Qed.

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03memh12pch24regsh33romh41vh52x8p;1p;2p;7p;5p;3g001Zj10Tg002?j1ATg002dj11Tg003Bj12Tg0000j2@Tg003ej1:Tg005Ij28Tg00XMj75Tg00=^j56Tg00YHj27Tg00ZHj14Tg00;Aj13Tg00;_j29Tg00<Bj3?Tg00[Ej3>Tg00\@j2;Tg009Lj5<Tg005kj3=Tg00@l#0R0#AR1#1R2%00R0#0R3#0#0#0#1#2R4'@%13#2#:\4R3p,2fxR5f5R6f4R7f1R8,84f3R9f2R:f0R;F5g00BQP6P7P9P:P8D6/7;#4P5%01#3R1g00CX1921d5?2=>6;%30,;7P9P:D<3=eX44X54X33W0X14W2o"). Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03memh12pch21rh34regsh43romh52x8p;1p;2p;7p;5p;6p;3g001Zj10Tg002?j1DTg002dj13Tg003Bj14Tg0000j2CTg003ej1;Tg00];j7:Tg00=^j58Tg001:j17Tg00^:j22Tg00^Zj11Tg00_:j66Tg00`8j29Tg00ZHj1BTg00;Aj15Tg00;_j2ATg00<Bj3<Tg00[Ej3=Tg00\@j2>Tg009Lj5?Tg005kj3@Tg00@l#0R0#DR1#3R2%00R0#0R3#0#0#0#3#4R4'C%33#4R3#;\4R5p,2fxR6f5R7f4R8f1R9f3R:f2R;f0R<F:g00BQP7P8P:P;P9D8P<%73,24#11244#1R3P3g00a1#1g00ai,24#1E6'9#BP6%01#5R1g00CX1A21d5<2==7<%50,>8P:P;D?3@eX24X54X45W0X14W3o"). Qed.

Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h01mh13memh22pch31rh45readsh54regsh63romh72x8p;1p;2p;5p;3p;6g001Zj10Tg002?j1GTg002dj13Tg003Bj14Tg0000j2FTg003ej1@Tg00^:j22Tg001:j16Tg00=^j5:Tg00YHj28Tg00ZHj17Tg00;Aj15Tg00<Bj39Tg00[Ej3ETg00\@j2DTg009Lj5CTg005kj3?Tg00bHj6>Tg00^Zj11Tg00_:j6=Tg00cWj2ATg00`8j2BTg00dRj3<Tg000\j6;Tg00@l#0R0#GR1#3R2%00R0#0R3#0#0#0#3#4R4'F%33#4R3#@\4R5g00ai,24R6#6g00BQR7f6R8f5R9f4R:f3R;f2R<D:R=f1R>'8f0R?#7p,2fxf7%01#5g00CX592;E<%50,D8P9P:DC5?7X07P8P9P:P;P<P>E>P>%63,24#11244#1R3P3g00a1#1%16E=,A?,B=A<=>?E;W4X34X74X65W1X24W5o"). Qed.

(* [comment removed for export] *)
Lemma rz_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h02HEh12HFh22Hch32Hhh45Hlazyh51Th63memh75modelh82pch94regsh:3romh;4segsh<1wp;1p;2p;3p;5p;8p;:g001:j19Tg001Zj10Tg002?j18Tg002dj12Tg003Bj13Tg0000j2CTg003ej14Tg00ebj1?Tg00fYj1=Tg005kj31Tg00^:j2<Tg00g;j1;Tg00^Zj1:Tg004Gj2JTg005Ij2ITg006Ej1HTg00;Aj1BTg00;_j2ATg00<Bj36Tg00<ej25Tg00=^j57Tg00h3j2@Tg00hhj3>Tg009Lj5DTg00D4j2ETg00igj8FTg00k9l:GTg00?m#9g00@l#0R0#8#2R1%00#0R0#0#0R2#0#2#3R3'C%20#3#4\3R4g00l5%22#3R2g00lk%43R5f2R6#?%=3R7311<33R8#9f3R9#;%:831%42f9R8f7R:'J1I2931g00AQf4R2#Hg00B131f;R;f:R<P8f8R=P:%80#BR0g00CXR>1A10d561,5<D7f6R?'@;>2f<R@p,2fxP;P<P8P=DDP:P;P<P8P=A610>,5;D7f5P2P91E57P@P;P<P8P=P?P6f1GFf0M:GW2W0W1W4W3W5W<W7X:4W6X83W9W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_write_chan : forall segs regs pc mem model fd ch n bs T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 64%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdChannel ch) -> w_is0 ch = false ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
  (1 <= n)%nat -> (Z.of_nat n <= rw_bytes_max)%Z -> (Z.of_nat n < 2 ^ 64)%Z ->
  rdn segs mem (getr regs 11) n = Some bs ->
  (forall k, (1 <= k)%nat -> (k <= n)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) T) ->
  realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
           (t_write_ch ch bs T).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h04__x1h13Hk0h21nh32Hah45Hlen0h53Hn0h67__arithh74__ffh87__sat66h97__sat67h:7__sat68h;8__varmaph<5__with=4__x2h>4__x3h?1bh@4cstrhA5cstr0hB1xhC7__sat65hD5cstr1hE4__p1hF4__x4hG1khH1yhI1HhJ3H65hK2HchL3HchhM4HcnthN3HfdhO5Hfd32hP2HhhQ3Hk1hR3Hk2hS5HlazyhT4HlenhU3HlkhV4HmaxhW3Hn1hX4Hn64hY3HnohZ3Hrdh[1Th\7__sat69h]2bsh^2chh_2fdh`1mha3memhb5modelhc1ohd2pche4regshf4segshg1zhh3z65p%0p&0p;1p;2p;3p;4p;5p;6p;<p;7p;8p;Cp;Bg001:j1UTg001Zj1>Tg002?j1LTg002dj1\Tg003Bj1wTg0000k20OTg003ej1QTg00ebk10CTg00fYj1lTg005kj31j1tTg00^:k204Tg00g;k100Tg00^Zj1vTg00;Aj1=Tg00;_j2TTg00<Bj3@Tg00<ej29Tg00E8j2cTg00mdj2sTg00nAj2<Tg00n]j1pTg00oQj2oTg010Ij1nTg005Ij2FTg011Aj1mTg00I2R0j10Tg00Ioj2Ck107Tg00P]j1WTg012;R1j28Tg012UR2j22Tg0131j4ITg00[Ej3YTg00\@j2gTg013ij1STg009Lj5bTg00h3j2dTg00hhj3eTg014ej6yTg015dj26Tg00=^j5hTg016Dk40YTg016_k30XTg017Xk20WTg00D4j2JTg00KTj2NTg018Tk50VTg000\j67Tg019cj3fTg01:hk10NTg01;fk10MTg01<aj1uTg01=Ak10JTg01=_k20ITg01>Bk30GTg01>_j4;Tg01?Fj1?Tg01?kj2rTg01@Sj3qTg01A7j2PTg01AUk10FTg01B3k10ETg01B^j2_Tg01CAj2KTg01Cdk30BTg01DGj4^Tg01E2k20ATg01ETk20@Tg01F@k30?Tg01F_k40>Tg00MNj2HTg01GQk20=Tg01HMk50<Tg01IRk50;Tg01Jak50:Tg01L0k109Tg01Lnj3kTg01MMj2jTg01NEj2ZTg01N\R3j2XTg01O9k106Tg01OWl<[Tg01P<k203Tg01P^j2iTg01Q8j2GTg01Qaj2OTg01RMk102Tg01Rkk201Tg01SLk30DTg01T5j3RTg01TUj4VTg01U3j6~Tg01UWj7}Tg01V;j4aTg01Vfk80HTg01WCj3|Tg01Wek10KTg00FFk60LTg00YHj2{Tg00ZHj1zTg00bHk60PTg01XCmC0QTg01YCk70RTg01Ygk70STg01ZKj8xTg01ZomB0TTg01[Um<0UTg01\:k30ZTg00MiR4f1R5f0R631p=41J46p=3g00aiR7P4P6P0P5f2R8f3R9f4R:f5R;f6R<f7R=f8R>M<[p=`P7P4P1P0P2g01\cP;P:P9P8P5P6M<[p=Ag00LRR2/26p=5P4P5g01]EP6C^p=DP5g01]lR1g01^KR?P?g01^kR@P6g01_KK0Rp=:P8P1P?P?P@P5P6K0Sp=]P9P1P?P?P@P8P5P6Gxp=BP7P7P7P4P4P4g01_kP0P0P0P3g01`KP;P:P9P8P5P6NB0Tp>05P7P4P4P4P0P0P;P:P9P8P5P6N<0Up>08B0Z456p=EP4P5g01`nP6C^p=Mg00?m#Ug00@lR0#>R3#LRA#\RB%>3RC#>RD#>#>RE#>RF#\RG#wRH+0O%\D#wRI#Q\HRJg00l5%UIRKg00lk%QHRL&0C;%lH31204HHRM#U&00<%vM31f:RM%LD#=RDg00CXRN1TBDd5@B'9,cG%=FRF'4f;RO%>A#=RPPN1TBPd5@BRQ'9=1H=1cG>%=3RR%=ERE'sRS'<g01aURT#QRU%pMf9RV'o%n>,FT31g00AQRW%mVg01bMRX31f?RY%L0S00#>S01#>#=RZPN1TBZd5@B'9%0VR[,CG51Hg00O@R\#WR]/8M%0Og01bmR^'2f<R_#01sRFR`'<%QKRafDRbfARcfCRd%LA#=RePN1TBed5@B'9f=S02CI1FK_3118]6Rff@Rg,85fHRhp,2fxS03fGRi%08Rj,CGS047YQfFRQ%=CRC'gfERk%ShRlDb/db;eY[[^G7PQPdPYA@BeNRe,9kf>RmP5Ey16Im=17YPiPQPkPb%SiRnA@BDNRD,9QRoDhRpPdfBRqPcPoPYPmQ02P_%pd/oq%nc,FT51U%mc=1WXP>P=H0YB0Xqcde20WqV1FHo,JLPOPHA@BPNRP,9QA1H6dX?HPM1Np\PQPkPbPnPoI0VE7PH19QeRLPiPQPkPl19iDDhRl%W]R>,Nl7f61FKgRX51aX?HPHA@BZN,9QS0519ieRe=fl6=1aXX?HRlPH%0gRZ,CGRNPlPaPi&0NpPL&0MNS06CIRlA1a6XXcaP4PZPhPkPe%u6CI=1aXXg4P7PgPhPkPeP6CI=1aXX27P8%uZ&0JgE71cGN16IYRX=17g%0XRe/4ZRB%t7S07%t4RU%05%06RT'4A175620I5640GXH7XB7S08PXPe%3ePgPZ%3ZM9`P6C;PB18]c%=0RB%0cRe'2RmP]PB%3BRrPcPe%3eEAP<C;Pm16IcRc#?%0c#5%?d%0dRm#51rRERe1<2RRs%5E1<2S[[Rt%5RRug00NdRvAqRE5UW3RE%5S\v^3uRS1rRFRw%5F1<2`[\sRsAqRF5VvX3uRF%5`\v^3uRug01cnRv#vRx%UvRy1P45S09&0F4Rz&0E4R{1_4B1K40R|'D,:{S0:%l?R}P{P4P|g01dZ1_4R>0B4GC^,:{RRP}1_42/D|,:{=]{RCBCB20A{@RRP6P8g00B1R~,JW20@68=1W~dB0?425H0>R2b7b;b<X0412B6R~1<5`%581<8`'H[[^04P6fIR`#0RWP=P_O3b6bCb8b9b:bAb@b5b4-0=ZE7PiPbPLQ06CI1FKYRK51aeA1alKeAfpLNPiPpPLPN1JJnI0<E7Q05P<E71Np>PQPkPbPnPoI0;E71Np]PQPkPbPnPoI0:E7P7Pg12T^X27P:PXP6E7&09YeP7PgPfX27P;PXP6E7185cg00BQRcQ03AkI8qRX,jIRg9Y`P1ghCPifJR^#SRoDbfKRn1d6i;eqX`cP716IqRc,Z8%09Rp,CGRJ1CGT51HX27P7Pd1Z96#0,CG91HJX27P4PH&07GRGPGPj1Z8dRN#0RLPH\4/JG14jL1XjmRG,4jP4P4PUP6XB4RKPU1456Rl$06XH4XB4PjPj%3jRaPLPGPKPK%3TXB7PNPGP8PjPaPdPm%3mJ05J08M<[188c%0cRm,2jRGP8PjPaPcPm%3mEAP6C;PG18]9RG12BpRmP]PBPrP9Pp%3pRaEARjP8C;Pm16IbRN=17k%0NRT%0kRK'4RLQ07PUQ08PNPT%3TPkPK%3KM9`P;C;PL18]Q%0QRL,2BRKP]PBPrPQPL%3LRTEAPOC;PK%?<%0<#516IiRK#?%0K#5%?`%5W%0^RW-03[1<[W1X[WRK/4['H12W[14KW'H'i%0M%0n'XP4PePtPEPSPwPsPFPup-0RK%W>R[#W,G41G4[R[1G4\R\'E'Eg01eARN'O&020-014>0D4[R[1G4>1G4]/E\'ER>'E/ON1E[\/ON=Rvx5Rv5RvPyP41P48P5P41P49R[P:1P4:CVCVPzP{P{P1P?P?P@P{P1P?P?P@P<E~1K43R3/M|,:{5]{1K4ARA/D|,:{1M3A,:{5]{F}P}P{Q00#L,K4R@/MA,:{P}P{1D|@,:{P}1M|3,:{CBCBCBPRP2b7b;b<X04X=4X>4XF4WE1H:l12861458'H'i14:9128;149:[[[^04^=4^>4^F4^EKP6fQ#0RK,<ZfPRl,6I#0PKP;PZP<POQ02O8b6b8b9b:b\bhbJbDbAb@b5b4b1b1CaL0HPcP9E716IXA|I8qE7Q04=1HgRqePqPHPJfLRJQ03AYnP61g^CP`%SJDb/dh;edX?HP;P9PGPmPj16IdRj,89%0jRm,2pRGP9PpPaPjPm%3mEAP5C;RmPG18]:%0:Rj,2BR;P]PBPrP:Pj%3jEAP9C;RjP;16IkRk=17Q%0kR:/4LRJQ07PUQ08PkP:%3:PQPLPTM9`P<C;R<PJ18]i%0iRT,2BRLP]PBPrPiPT%3TEAP_C;R_PL%?=RT%0=#5R=16IhRr#?R]%0r#5Rr%?^R^%5WRWPePtPEPSPwPsPFPuPxPyQ09PzP{Q0:P}Q0:CBPRP2b7b;b<X0412B5\~^04P6%0YRYPMO2b6bCb8b9b:bDbAb@b5b4b1b1Ca189b%0bRM,2pP9PpPaPbPM%3MEAPmPGPjP;P<PJP_PLPTP=P]PrP^PWPePtPEPSPwPsPFPu1O>N=RvxPyP4P4&0K4RyP8P[CVP5PyCVPzP{Q01,K4Rz/M3,:{P}P{1D|z,:{P}1D|3,:{CBCBPRP2b7b;b<X04X=4X>4148512591289[[^04^=4^>4P6fO,6I#0%0lPYPVPOO5b6bCb8b9b:bDbAb@b5b4b1b1CaO3AkI9d,jIP6J0LbIP`PhPiPo19`DRDDh/{g#zP`PhPiPoPDPgJ0PE7WRXQfXG7NC0QbTWKWZWXWVWWWMWLWUWOWNWYWSWPW[W]X27X^HX_HWbWaXdHWeWfo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h01Hh12H0h22Hah37__arithh44__ffh58__varmaph65__with74__x1h81zh96__sat0h:6__sat1h;2b1h<2b2h=1nh>2Hch?4codep;1p;2p;3p;4p;6p;7p;8g001Zj12Tg00;Aj1:Tg00nAj20Tg00MNR0j26Tg003Bj18Tg005kj39Tg00E8j23Tg00Ebj3NTg002dj1CTg00Ioj2BTg002?j14Tg01emj3aTg01fRj2>Tg00mdj2HTg01g0j2ZTg01?kj2FTg01@Sj3ETg00^Zj1XTg001:j1WTg01A7j2VTg01AUj1STg01B3j1RTg01CAj2QTg01B^j2;Tg00fYj1MTg01Cdj3DTg01E2j2LTg00D4j2KTg01ETj2OTg01F@j3PTg01F_j4JTg01gPj3TTg01h3j1UTg01Wej1`Tg01hQj3_Tg000\j6?Tg01GQj2ITg01i4j3^Tg012Uj2]Tg01DGj4GTg01YCj7[Tg01Ygj7\Tg01ZKj8YTg00LRR1f0R2']p=1g00MiR3f1R4;92p=7P3P4g01dZP2CGp==P4g01]lR5g01^KR6P6g01^kR7P2g01_KF[p=5P3P4g01]EP2CGp=Af2R8P5P6P6P7P4P2F\p=@f3R9P5P6P6P7P8P4P2GYp=<%12g00@lR5#2R:#2#2R;#2#2#2R<#2#2#:R=,02R>'6g00M0R?%82R@%84RAP0%88?94213981394'7RB[13841382'7%89?984[RCf4RD#8?998\BAN842P2n2001000000120000000W<W;W=PC^<A^;@^=?P2%C<R?1B?8R@%45#4#4#4#4#4#4#:RA,B?RC5a?RBP@P313?@RE13?CRF'>1B?9,3?,72X83P3P81>2F/72X83P3PA1>92/79X83P3%::R:%:;RG'HRH,Z81729X831F:G101:RI%1GRJ101H[[%1:RKg00NdRLAE:G4UW2%1H\L^2KP0%1DRM10D=RDf5RN#1RO10NH'6P9f6#1RPf7/0=RQg01cnRR#XRS%WRRR1V34RT%S3RU%R3RV1Q35R51;3='=,5VRW%M6R6PV1;31RX/A5,5VRYP61;3:RZ%C;5D3,=5,5V9@VYC<C<1LV7R7P2P8g00AQR;g00B1R['K1O28=9;[dAP314CJR[b4b5b6X73%14R;%18R\108H'6[\>^73P2f9P4P8O3R]b3W1W0P4P2O2n2001000000120000000b9b:9T8H%UG,>8P0P\108=PJP410N=PSPR%`3R=PU1;3G,AX,5VP7P[b4b5b6PJP2b3W1X0MP4P2O2n20010000001200000009_8GE?PF%:<R<,F:RF%1<1H:<RG,01[\IRIAE:<4VLX2KR<%1G\L^2KRKP0PMPD%1A10AG'6RLP9PSPRP=PU1;3AR=,AX,5VAD3Z?RZ,==,5V5@VP7P[b4b5b6PLP2b3X1QX0PP4P2O2n2001000000120000000b9b:,IAE?PEPFPIP<PKP0PMPD10NG,6OP9PSPRPTPUPVPWP6PVPYP61=5Z,5V9@VYC<C<P7P[b4b5b6X73108G,6\\;\>^73P]b3X1QX0PP4P2O2n2001000000121000000b9b:,I8E?13?BA^?@CE?O4b0W>X?3o"). Qed.

Lemma rz_exit_lit : forall segs regs pc mem rom model code,
  m_halted model = None -> is_exit_no (getr regs 17) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model)
           (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h01bh13Ha0h22Hch32Hhh43Hx8h54codeh63memh75modelh82pch94regsh:3romh;4segsp;1p;2p;3p;5p;7p;6g001:j1OTg001Zj10Tg002?j11Tg002dj15Tg003Bj1?Tg0000j2MTg003ej1<Tg00ebj1DTg00fYj1BTg005kj3>Tg00;Aj14Tg00;_j28Tg00<Bj33Tg00<ej22Tg01ibj1NTg00Ioj27Tg012Uj2LTg00nAj2KTg00MNj2JTg01emj3=Tg00=^j5:Tg00h3j2ETg01j`j1CTg01kSj29Tg00hhj3;Tg00KTj2FTg005Ij2GTg00D4j2HTg01lNj7ATg018Tj5ITg00FFj66Tg01mJj2@Tg00?m#Og00@lR0#0R1#1R2#5R3%01#0R1#0#0#0R4#5R5#?R6'M%51#?#<\6R7g00l5g00Mi%<6R8f1R9#D%B63>f6R:%11#4R1g00CXR;1831d533'2#Nf7R<%02#4R2P;1832d533'2f2R=,755>6g00LRf3R>'L%04#0#4,K>'JP6f4R4,75R?%10#1#1#1#1#1#1#4,75R05=5f;R@f:RAf9RBf8RCP<A331;R1,2AD:/E:RDf0RE%C:RF'93;X06P6A332;,2BR2A=5E0/9F9;@DX06RDP6PBPCP<P:12B1R1D:R@g00O@'FPDPAP@f5P1P>1G61,H8P=FAP2PBPCP<P:P1DIE6P?P9E6P?1@4EE6W2W1W4W3W5W7X:7W6X86W9W;o"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall segs regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h01bh11Hh24codeh33H10h43H17h52HEh62HFh72Hhh85Hlazyh93memh:5modelh;2pch<4regsh=3romh>4segsh?1wp;1p;2p;3p;5p;6p;7p;=g001:j1DTg001Zj12Tg002?j11Tg002dj16Tg003Bj1:Tg0000j2RTg003ej18Tg004Gj2MTg005Ij2;Tg005kj30Tg006Ej1HTg00ebj1FTg00fYj1ETg00^:j2VTg00g;j1UTg00^Zj1TTg00;Aj14Tg00;_j2ATg00<Bj35Tg00<ej23Tg00Ioj29Tg01P^R0j2NTg01emj3?Tg01j`j1>Tg01kSj2<Tg00=^j5=Tg00h3j2LTg00hhj3KTg00KTj2ITg00D4j27Tg01ibj1JTg00E8j2BTg000\j6@Tg01n\j3GTg01o6j3OTg01lNj7PTg018Tj5QTg00FFj6CTg01oPl=STg00?m#Dg00@lR1#2R2#1R3#6R4%22#2R2#2#2R5#2#6R6#:R7'R%62#:#8\7R8g00l5%65#:R5%85f7R9f5R:'Mf1R;,;530g00AQf2R5#Hg00B130%87R<f4R=#F%E7301V77R>#D%U:%T>30f:R>%12#4R2g00CXR?1A42d554'3R@%13#1RA#1#2#4RB,96RC507%2A#1#4RA,96RD907@'Nf;R@%23#4R3P?1A43d554'3=07:f=REf<RFP@P>f9RGf8RHP9f6R9%11#1#1#1#1#1#1#4,96R15?6%>H'<f3RIP5P:P=P7A543?,3FR3f>R=PEPFP@P>A542?R?,3ER2D=/LGf0R4=?61%>G'<3KR1X27P7PFP@P>PG13F?R:D=R5g00O@'IP1X07PEP5PHP:PI1;7:,7<P0A07:CA07:D%J2P;A072Cg00MiR;13=?R?,B6R=;0AR0A0;=BR=P7PC1B64R6=0;BX0717;BP?P4E@3GW1P4O1A072DP7PDA0;6AX0717;AP?P4E@9O0=W1P4O1n200100000021100011000FPP3PFP@P>PGP:DQECP9P4ECM=SW3W4W8W7W5W6X27W?W:X=8W9X;7W<W>o"). Qed.

Lemma rz_exit_at_lit : forall segs regs (pc : word) mem rom model w (code : Z),
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodesG ()) ["G"] "h03H10h13H17h22HEh32HFh42Hch52Hhh65Hlazyh71bh84codeh93memh:5modelh;2pch<4regsh=3romh>4segsh?1wp;1p;2p;3p;5p;>p;6g001:j1;Tg001Zj11Tg002?j10Tg002dj15Tg003Bj17Tg0000j2LTg003ej16Tg004Gj2CTg005Ij2ATg005kj32Tg006Ej1?Tg00ebj1=Tg00fYj1<Tg00^:j2QTg00g;j1PTg00^Zj1OTg00;Aj13Tg00;_j2:Tg00<Bj38Tg00<ej29Tg00Ioj24Tg01P^j2ITg012Uj2BTg00nAj2DTg00MNj2ETg01emj3FTg009Lj5GTg00h3j2HTg01j`j1@Tg01kSj2JTg00hhj3KTg020Xl>>Tg01mJj2MTg00FFj6NTg00?m#;g00@lR0#1R1#0R2#5R3%11#1R1#1#1R4#1R5#5R6#7R7'L%51#7#6\7R8g00l5%54#7R4g00Mi%64f7R9f5R:'Cf1R;,A432g00AQf2R4#?g00B132%67f4R<#=%<7321Q77R=#;%P:%O=32f:R=%01#3R1g00CXR>1:31d583'9R1%02#0R?#0#1#3,46527%1?#0#3,469271'If;R1%12#3R2P>1:32d583'9146:527g00LRf6R3'B%15#1#3,D3'EP71469R5%00#0#0#0#0#0#0#3,465F6f?p,2fxf>R6f=R0f<R2P1DG/H=f0R>%@='J3KX77P6P0P2P1P=f9f8P5P3P:P<f3P4P;M>>P51M9>ENW4W0W1W6W5W2W3W8W?W:X=8W9X;7W<W>o"). Qed.

End G.
