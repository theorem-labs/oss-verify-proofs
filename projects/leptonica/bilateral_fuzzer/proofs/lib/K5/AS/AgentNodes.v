(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (writev's channel-reader flag; the address check on user-memory reads; recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AgentLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AgentNodes () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib2K52AS8PropExec:step_ecallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C69OSSVerify5KrLib2K52AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C69OSSVerify5KrLib2K52AS8PropExec4getrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes5ependC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib2K52AS:AgentNodes>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC69OSSVerify5KrLib2K52AS8PropExec7getr_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib2K52AS8PropExec9arg_reg_0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib2K52AS8PropExec9arg_reg_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec9arg_reg_2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes9arg_reg_3C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes9arg_reg_4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes9arg_reg_5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC69OSSVerify5KrLib2K52AS7CatExec7adv_setC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC69OSSVerify5KrLib2K52AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7FileSim;adv_eff_retC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib2K52AS:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC69OSSVerify5KrLib2K52AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I69OSSVerify5KrLib2K52AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes@step_ecall_ependC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C69OSSVerify5KrLib2K52AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K52AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K52AS6CatSim6fdchanC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idc69OSSVerify5KrLib2K52AS:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K52AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7CatExecAms_read_bytes_rdnC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega6VarMap1t01C69OSSVerify5KrLib2K52AS8ShapeAlg;rz_write_chC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes4bool02C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions?bv_and_unsignedC69OSSVerify5KrLib2K52AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC69OSSVerify5KrLib2K52AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52AS:AgentNodes@bv_and_255_smallC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : K5.AS.PropExec.FPState := K5.AS.PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

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
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh44segsh51wp;1p;2p;3p;9p;5g0000R0p4p7210p1000\p4p710p8g001:j1DTg001Zj10Tg002?j14Tg002dj11Tg003Bj13TP0j2<Tg003ej15Tg004Gj28Tg005Ij27Tg005kj32Tg006Ej16Tg007El99Tg008Cj1:Tg009Kj5CTg00:Cj2BTg00;?j1ATg00;]j2=Tg00<@j3>Tg00<cj2?Tg00=[j5;Tg00>Vj2@Tg00?^#Dg00@]#0R0#4#1R1%00#0R0#0#0R2#0#1#3R3'<%10#3#5\3R4%12#3R2%52f5R5f3R6'8f0R7,7232g00ABf1R2#6g00Ab32g00BBR8f7R9f6R:P5f4R;P6f2P2P7M99g00CFR7#:P8P:P5P;P6DC,B9P:P5P;P6%40#AR0g00DM1=10d5>1,?:D;,@732eUUW5X34W0X13W2W4o"). Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j17Tg002dj11Tg003Bj12Tg0000j26Tg003ej13Tg005Ij25Tg00Dij24Tg00@]#0R0#7#1%00#0R0#0#0#0#1#2R1'6%10#2#3\1R0%31f0,51'4X41X30W0X11W2o"). Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j1ITg002dj16Tg003Bj12Tg0000j2HTg003ej1CTg00;?j1<Tg00<@j35Tg00ECj27Tg00<cj24Tg005kj30Tg00Emj21Tg00FWj38Tg00G;j6GTg00GWj2FTg00H6j1ETg00HOj3BTg00IJj4=Tg00Ifj1>Tg00JFj2?Tg00Jcj2@Tg000\j6ATg00=[j5;Tg00KIj1:Tg00LHj2DTg00;]j29Tg00@]#3R0#IR1#6R2%30#3R0#3#3#3#6#2R3'H%60#2#C\3R0%22R4%31#<R1g00DMR5552R6f5R7f0R8'71476503X54P3f4R7/46R91776g00MFR:=525R;9046R4g00MdR<%28R=f1R>#2R?g00NBf2R@#2?0>8g00N]RAf3RB/1@11B>30[RC11@>11@850A%2B?0@>RD[117B117@50A\DA8@>8P>n2001000000120000000W3W2W4PC^3?^2=^4<P8P2P6P;P>O41126112;50APAP1PAp-0P8g00O;R;g00OXP;n011000003001000010000X6AP5P:P8EGP;1F;8b0b1b0W1%E4e9B76C=g00P4R6#>,?1,@2R4g00PSEAP7PBP@P>P8D;R8#:/74=039e1D86P51921d9521,47503eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j19Tg002dj17Tg003Bj13Tg0000j2JTg003ej1DTg00;?j18Tg00<@j35Tg00ECj24Tg00<cj26Tg005kj30Tg00Emj21Tg00FWj3:Tg00G;j6ITg00GWj2HTg00H6j1GTg00HOj3CTg00IJj4BTg00QPj1?Tg00Ifj1>Tg00JFj2@Tg00Jcj2ATg000\j6=Tg00=[j5<Tg00KIj1ETg00LHj2;Tg00;]j2FTg00@]#2R0#9R1#7R2%20#2R0#2#2#2#7#3R3'J%70#3#D\3R0%32R4%91#8R5g00DMR6552R7f5R8f0R9'41687503X54P3f4R8/67R:1487g00MFR;=526R<9047R4g00MdR=%39R>f1R?#3R@g00NBf2RA#3?0?9g00N]RBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA:A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P2P7P<P?O41127112<50BPBP5PBp-0P9g00O;R<g00OXP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G4e9C87CB%21#8g00P4#?R1#>'@,A2R7g00QoE=P8PCPAP?P9D<R9#E/47=03:e1;91P61F25d9525,68503eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j1:Tg002dj17Tg003Bj13Tg0000j2JTg003ej1DTg00;?j19Tg00<@j35Tg00ECj24Tg00<cj26Tg005kj30Tg00Emj22Tg00FWj3;Tg00G;j6ITg00GWj2HTg00H6j1GTg00HOj3CTg00IJj4BTg00QPj18Tg00Ifj1?Tg00JFj2@Tg00Jcj2ATg000\j6>Tg00=[j5=Tg00KIj1ETg00LHj2<Tg00;]j2FTg00@]R0#1R1#:R2#7R3%11#1R1#1#1#1#7#3R4'J%71#3#D\4R1%33R5%:0#1#1#9R0g00DMR6553R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00MFR;=536R<9057R5g00MdR=%39R>f1R?#3R@g00NBf2RA#3?0?9g00N]RBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00O;R<g00OXP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#9g00P4#8#8R2#?'@,A3R7g00RlE>P8PCPAP?P9D=R9#E/47=04:e1<92P61F30d9530,68504eX;4X:1W7X84W9o"). Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00Emj20Tg00FWj37Tg001Zj15Tg002?j14Tg002dj1<Tg00;?j16Tg00QPj13Tg00Ifj1;Tg00JFj28Tg00Jcj29Tg00<@j3:Tg00Dij2=Tg00MdR0f0R1#1R2f1R3#1R4g00NBf2R5#1?231g00N]R6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@]R1#5#4R0#<R2%50#6g00P4#3#3#3#;'8,92%41#5#4#6g00DM5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00Emj20Tg00FWj37Tg001Zj15Tg002?j14Tg002dj1<Tg00;?j16Tg00QPj13Tg00Ifj1;Tg00JFj28Tg00Jcj29Tg00<@j3:Tg00Dij2=Tg00MdR0f0R1#1R2f1R3#1R4g00NBf2R5#1?231g00N]R6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@]R1#5#4R0#<R2%50#6g00P4#3#3#3#3#;'8,92%41#4#5#6g00DM5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj10Tg005kj33Tg00Emj22Tg00FWj37Tg001Zj16Tg002?j14Tg002dj1<Tg00;?j15Tg00QPj11Tg00Ifj1;Tg00JFj28Tg00Jcj29Tg00<@j3:Tg00Dij2=Tg00MdR0f0R1#0R2f1R3#0R4g00NBf2R5#0?331g00N]R6f3R7/25127333R8[12531251536%07?353[R9f4#0?375\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@]R1#6#4R0#<R2%60#5g00P4#1#1#1#1#1#;'8,92%41#4#4#5g00DM5:2R11221,=6O4b3o"). Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j19Tg002dj15Tg003Bj13Tg0000j2JTg003ej1DTg00;?j1:Tg00<@j38Tg00ECj24Tg00<cj26Tg005kj30Tg00Emj22Tg00FWj3;Tg00G;j6ITg00GWj2HTg00H6j1GTg00HOj3CTg00IJj4BTg00QPj17Tg00Ifj1?Tg00JFj2@Tg00Jcj2ATg000\j6>Tg00=[j5=Tg00KIj1ETg00LHj2<Tg00;]j2FTg00@]R0#1R1#9R2#5R3%11#1R1#1#1#1#5#3R4'J%51#3#D\4R1%33R5%90#1#9#:R0g00DMR6583R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00MFR;=836R<9057R5g00MdR=%39R>f1R?#3R@g00NBf2RA#3?0?9g00N]RBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00O;R<g00OXP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#:g00P4#7#7#7R2#?'@,A3R7g00SiE>P8PCPAP?P9D=R9#E/47=04:e1<92P61F30d9830,68504eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j19Tg002dj15Tg003Bj13Tg0000j2JTg003ej1DTg00;?j1:Tg00<@j38Tg00ECj26Tg00<cj27Tg005kj30Tg00Emj22Tg00FWj3;Tg00G;j6ITg00GWj2HTg00H6j1GTg00HOj3CTg00IJj4BTg00QPj14Tg00Ifj1?Tg00JFj2@Tg00Jcj2ATg000\j6>Tg00=[j5=Tg00KIj1ETg00LHj2<Tg00;]j2FTg00@]R0#1R1#9R2#5R3%11#1R1#1#1#1#5#3R4'J%51#3#D\4R1%33R5%90#9#1#:R0g00DMR6583R7f5R8f0R9'61787504X55P4f4R8/77R:1687g00MFR;=836R<9057R5g00MdR=%39R>f1R?#3R@g00NBf2RA#3?0?9g00N]RBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00O;R<g00OXP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#:g00P4#4#4#4#4R2#?'@,A3R7g00ThE>P8PCPAP?P9D=R9#E/67=04:e1<92P61F30d9830,78504eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j15Tg002dj16Tg003Bj12Tg0000j2JTg003ej1DTg00;?j1:Tg00<@j38Tg00ECj29Tg00<cj27Tg005kj30Tg00Emj21Tg00FWj3;Tg00G;j6ITg00GWj2HTg00H6j1GTg00HOj3CTg00IJj4BTg00QPj14Tg00Ifj1?Tg00JFj2@Tg00Jcj2ATg000\j6>Tg00=[j5=Tg00KIj1ETg00LHj2<Tg00;]j2FTg00@]R0#3R1#5R2#6R3%31#3R1#3#3#3#6#2R4'J%61#2#D\4R1%23R5%50#5#5#:R0g00DMR6583R7f5R8f0R9'91787504X55P4f4R8/77R:1987g00MFR;=836R<9057R5g00MdR=%29R>f1R?#2R@g00NBf2RA#2?0?9g00N]RBf3RC/1A11C?30[RD11A?11A950B%2C?0A?RE[118C118A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41137113<50BPBP0PBp-0P9g00O;R<g00OXP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%32#:g00P4#4#4#4#4#4R2#?'@,A3R7g00UgE>P8PCPAP?P9D=R9#E/97=04:e1<92P61F30d9830,78504eX;4X:1W7X84W9o"). Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h04addrh13memh22pch34regsh44segsh52x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00Vfj24Tg00Dij25Tg00?^#8g00@]#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1P0^01f4f1'4'5X51W1X21W3W4o"). Qed.

Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
  ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h04addrh13memh22pch34regsh43romh54segsh62x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00W\j24Tg00Dij25Tg00?^#8g00@]#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1R2P0^01f5f2'4'5X61X42W1X21W3W5o"). Qed.

Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00Dij23Tg00@]#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f2,30X41X30W0X11W2o"). Qed.

Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00Dij23Tg00@]#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f1,30X41X30W0X11W2o"). Qed.

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh41vh52x8p;1p;2p;7p;5p;3g001Zj10Tg002?j1ATg002dj11Tg003Bj12Tg0000j2@Tg003ej1:Tg005Ij28Tg00XYj75Tg00=[j56Tg00YSj27Tg00ZSj14Tg00;?j13Tg00;]j29Tg00<@j3?Tg00[Pj3>Tg00\Jj2;Tg009Kj5<Tg005kj3=Tg00@]#0R0#AR1#1R2%00R0#0R3#0#0#0#1#2R4'@%13#2#:\4R3g00BBR5f5R6f4R7f1R8,84f3R9f2R:f0R;F5g00CFP6P7P9P:P8D6/7;#4P5%01#3R1g00DM1921d5?2=>6;%30,;7P9P:D<3=eX44X54X33W0X14W2o"). Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch21rh34regsh43romh52x8p;1p;2p;7p;5p;6p;3g001Zj10Tg002?j1DTg002dj13Tg003Bj14Tg0000j2CTg003ej1;Tg00]Dj7:Tg00=[j58Tg001:j17Tg00^Bj22Tg00^bj11Tg00_Bj66Tg00`@j29Tg00ZSj1BTg00;?j15Tg00;]j2ATg00<@j3<Tg00[Pj3=Tg00\Jj2>Tg009Kj5?Tg005kj3@Tg00@]#0R0#DR1#3R2%00R0#0R3#0#0#0#3#4R4'C%33#4R3#;\4R5g00BBR6f5R7f4R8f1R9f3R:f2R;f0R<F:g00CFP7P8P:P;P9D8P<%73,24#11244#1R3P3g00a9#1g00b1,24#1E6'9#BP6%01#5R1g00DM1A21d5<2==7<%50,>8P:P;D?3@eX24X54X45W0X14W3o"). Qed.

Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h01mh13memh22pch31rh45readsh54regsh63romh72x8p;1p;2p;5p;3p;6g001Zj10Tg002?j1GTg002dj13Tg003Bj14Tg0000j2FTg003ej1@Tg00^Bj22Tg001:j16Tg00=[j5:Tg00YSj28Tg00ZSj17Tg00;?j15Tg00<@j39Tg00[Pj3ETg00\Jj2DTg009Kj5CTg005kj3?Tg00bPj6>Tg00^bj11Tg00_Bj6=Tg00cSj2ATg00`@j2BTg00dNj3<Tg000\j6;Tg00@]#0R0#GR1#3R2%00R0#0R3#0#0#0#3#4R4'F%33#4R3#@\4R5g00b1,24R6#6g00CFR7f6R8f5R9f4R:f3R;f2R<D:R=f1R>'8f0R?#7g00BBf7%01#5g00DM592;E<%50,D8P9P:DC5?7X07P8P9P:P;P<P>E>P>%63,24#11244#1R3P3g00a9#1%16E=,A?,B=A<=>?E;W4X34X74X65W1X24W5o"). Qed.

(* [comment removed for export] *)
Lemma rz_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02HEh12HFh22Hch32Hhh45Hlazyh51Th63memh75modelh82pch94regsh:3romh;4segsh<1wp;1p;2p;3p;5p;8p;:g001:j19Tg001Zj10Tg002?j18Tg002dj12Tg003Bj13Tg0000j2CTg003ej14Tg00e]j1?Tg00fTj1=Tg005kj31Tg00^Bj2<Tg00g6j1;Tg00^bj1:Tg004Gj2JTg005Ij2ITg006Ej1HTg00;?j1BTg00;]j2ATg00<@j36Tg00<cj25Tg00=[j57Tg00gnj2@Tg00hcj3>Tg009Kj5DTg00Dij2ETg00iaj8FTg00jgl:GTg00?^#9g00@]#0R0#8#2R1%00#0R0#0#0R2#0#2#3R3'C%20#3#4\3R4g00kb%22#3R2g00lX%43R5f2R6#?%=3R7311<33R8#9f3R9#;%:831%42f9R8f7R:'J1I2931g00ABf4R2#Hg00Ab31f;R;f:R<P8f8R=P:%80#BR0g00DMR>1A10d561,5<D7f6R?'@;>2f<R@g00BBP;P<P8P=DDP:P;P<P8P=A610>,5;D7f5P2P91E57P@P;P<P8P=P?P6f1GFf0M:GW2W0W1W4W3W5W<W7X:4W6X83W9W;o"). Qed.

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
  m_channel_reader model = true ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat n) ->
  (1 <= n)%nat -> (Z.of_nat n <= rw_bytes_max)%Z -> (Z.of_nat n < 2 ^ 64)%Z ->
  rdn segs mem (getr regs 11) n = Some bs ->
  (* the range [vfs_write]'s [access_ok] accepts on the count [n]; see
     [CatSim.write1_check_n] *)
  access_okb (getr regs 11) (Z.of_nat n) = true ->
  (forall k, (1 <= k)%nat -> (k <= n)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) T) ->
  realizes segs (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
           (t_write_ch ch bs T).
Proof.
  intros segs regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hrdr Hcnt Hn1 Hmax Hn64 Hrd Hok Hc.
  pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
  eapply (rz_write_ch segs _ model fd ch (getr regs 17) bs T Hh Hlazy).
  - unfold fdchan. split; [exact Hlk | split; [exact Hch | exact Hrdr]].
  - apply fd32_id. exact Hfd32.
  - reflexivity.
  - exact Hno.
  - rewrite ms_gpr_epend0. exact Hfd.
  - rewrite ms_gpr_epend1, ms_gpr_epend2, Hcnt.
    rewrite (ms_read_bytes_rdn segs) by reflexivity. cbn [ms_mem epend].
    unfold word_to_nat. rewrite u64_lit by lia. rewrite Nat2Z.id. exact Hrd.
  - rewrite ms_gpr_epend1, ms_gpr_epend2, Hcnt, u64_lit by lia. exact Hok.
  - unfold buf_modeled. rewrite Hlen. exact Hmax.
  - rewrite Hlen. exact Hn1.
  - intros k Hk1 Hk2. rewrite adv_set_epend.
    replace (len_word (firstn k bs)) with (Z_to_bv 64 (Z.of_nat k)); [apply Hc; lia|].
    unfold len_word. rewrite length_firstn, Hlen. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h01Hh12H0h22Hah37__arithh44__ffh58__varmaph65__with74__x1h81zh96__sat0h:6__sat1h;2b1h<2b2h=1nh>2Hch?4codep;1p;2p;3p;4p;6p;7p;8g001Zj12Tg00;?j1:Tg00mmj20Tg00NBR0j26Tg003Bj18Tg005kj39Tg00Emj23Tg00FWj3NTg002dj1CTg00Jcj2BTg002?j14Tg01dmj3aTg01eRj2>Tg00mPj2HTg01f0j2ZTg01?Gj2FTg01?oj3ETg00^bj1XTg001:j1WTg01@Sj2VTg01A1j1STg01AOj1RTg01B]j2QTg01B:j2;Tg00fTj1MTg01C@j3DTg01DNj2LTg00Dij2KTg01E0j2OTg01E\j3PTg01F;j4JTg01fPj3TTg01g3j1UTg01Vfj1`Tg01gQj3_Tg000\j6?Tg01Fmj2ITg01h4j3^Tg012Aj2]Tg01Ccj4GTg01XCj7[Tg01Xgj7\Tg01YKj8YTg00MFR1f0R2']p=1g00N]R3f1R4;92p=7P3P4g01cZP2CGp==P4g01\lR5g01]KR6P6g01]kR7P2g01^KF[p=5P3P4g01\EP2CGp=Af2R8P5P6P6P7P4P2F\p=@f3R9P5P6P6P7P8P4P2GYp=<%12g00@]R5#2R:#2#2R;#2#2#2R<#2#2#:R=,02R>'6g00MdR?%82R@%84RAP0%88?94213981394'7RB[13841382'7%89?984[RCf4RD#8?998\BAN842P2n2001000000120000000W<W;W=PC^<A^;@^=?P2%C<R?1B?8R@%45#4#4#4#4#4#4#:RA,B?RC5a?RBP@P313?@RE13?CRF'>1B?9,3?,72X83P3P81>2F/72X83P3PA1>92/79X83P3%::R:%:;RG'HRH,Z81729X831F:G101:RI%1GRJ101H[[%1:RKg00OXRLAE:G4UW2%1H\L^2KP0%1DRM10D=RDf5RN#1RO10NH'6P9f6#1RPf7/0=RQg01bnRR#XRS%WRRR1V34RT%S3RU%R3RV1Q35R51;3='=,5VRW%M6R6PV1;31RX/A5,5VRYP61;3:RZ%C;5D3,=5,5V9@VYC<C<1LV7R7P2P8g00ABR;g00AbR['K1O28=9;[dAP314CJR[b4b5b6X73%14R;%18R\108H'6[\>^73P2f9P4P8O3R]b3W1W0P4P2O2n2001000000120000000b9b:9T8H%UG,>8P0P\108=PJP410N=PSPR%`3R=PU1;3G,AX,5VP7P[b4b5b6PJP2b3W1X0MP4P2O2n20010000001200000009_8GE?PF%:<R<,F:RF%1<1H:<RG,01[\IRIAE:<4VLX2KR<%1G\L^2KRKP0PMPD%1A10AG'6RLP9PSPRP=PU1;3AR=,AX,5VAD3Z?RZ,==,5V5@VP7P[b4b5b6PLP2b3X1QX0PP4P2O2n2001000000120000000b9b:,IAE?PEPFPIP<PKP0PMPD10NG,6OP9PSPRPTPUPVPWP6PVPYP61=5Z,5V9@VYC<C<P7P[b4b5b6X73108G,6\\;\>^73P]b3X1QX0PP4P2O2n2001000000121000000b9b:,I8E?13?BA^?@CE?O4b0W>X?3o"). Qed.

Lemma rz_exit_lit : forall segs regs pc mem rom model code,
  m_halted model = None -> is_exit_no (getr regs 17) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model)
           (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h01bh13Ha0h22Hch32Hhh43Hx8h54codeh63memh75modelh82pch94regsh:3romh;4segsp;1p;2p;3p;5p;7p;6g001:j1OTg001Zj10Tg002?j11Tg002dj15Tg003Bj1?Tg0000j2MTg003ej1<Tg00e]j1DTg00fTj1BTg005kj3>Tg00;?j14Tg00;]j28Tg00<@j33Tg00<cj22Tg01hbj1NTg00Jcj27Tg012Aj2LTg00mmj2KTg00NBj2JTg01dmj3=Tg00=[j5:Tg00gnj2ETg01i_j1CTg01jRj29Tg00hcj3;Tg00LHj2FTg005Ij2GTg00Dij2HTg01kLj7ATg018<j5ITg00G;j66Tg01lGj2@Tg00?^#Og00@]R0#0R1#1R2#5R3%01#0R1#0#0#0R4#5R5#?R6'M%51#?#<\6R7g00kbg00N]%<6R8f1R9#D%B63>f6R:%11#4R1g00DMR;1831d533'2#Nf7R<%02#4R2P;1832d533'2f2R=,755>6g00MFf3R>'L%04#0#4,K>'JP6f4R4,75R?%10#1#1#1#1#1#1#4,75R05=5f;R@f:RAf9RBf8RCP<A331;R1,2AD:/E:RDf0RE%C:RF'93;X06P6A332;,2BR2A=5E0/9F9;@DX06RDP6PBPCP<P:12B1R1D:R@g00P4'FPDPAP@f5P1P>1G61,H8P=FAP2PBPCP<P:P1DIE6P?P9E6P?1@4EE6W2W1W4W3W5W7X:7W6X86W9W;o"). Qed.
