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
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AgentLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AgentNodes () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC59OSSVerify5KrLib2AS8PropExec:step_ecallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes5ependC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2AS:AgentNodes>asanreflect_fxC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib2AS8PropExec7getr_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib2AS8PropExec9arg_reg_0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib2AS8PropExec9arg_reg_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9arg_reg_2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes9arg_reg_3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes9arg_reg_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes9arg_reg_5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7FileSim3mrbC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib2AS7CatExec7adv_setC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7FileSim;adv_eff_retC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib2AS:AgentNodes=adv_set_ependC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC59OSSVerify5KrLib2AS6CatSimMapply_effect_copyins_no_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes@step_ecall_ependC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_stepC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:rdn_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic3and01C59OSSVerify5KrLib2AS6CatSim6fdchanC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idc59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend0C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib2AS8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExecAms_read_bytes_rdnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes=ms_gpr_epend1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS6CatSim;buf_modeledC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib2AS8ShapeAlg;rz_write_chC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes4bool02C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions?bv_and_unsignedC59OSSVerify5KrLib2AS7ExitSim:is_exit_noC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib2AS8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg7rz_exitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AgentNodes@bv_and_255_smallC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
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
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh44segsh51wp;1p;2p;3p;9p;5g0000R0p4p7210p1000\p4p710p8g001:j1DTg001Zj10Tg002?j14Tg002dj11Tg003Bj13TP0j2<Tg003ej15Tg004Gj28Tg005Ij27Tg005kj32Tg006Ej16Tg007El99Tg008@j1:Tg009Hj5CTg00:=j2BTg00;9j1ATg00;Wj2=Tg00<:j3>Tg00<]j2?Tg00=Rj5;Tg00>Jj2@Tg00?R#Dg00@Q#0R0#4#1R1%00#0R0#0#0R2#0#1#3R3'<%10#3#5\3R4%12#3R2%52f5R5f3R6'8f0R7,7232g00A6f1R2#6g00AV32g00B6R8f7R9f6R:P5f4R;P6f2P2P7M99g00C7R7#:P8P:P5P;P6DC,B9P:P5P;P6%40#AR0g00D>1=10d5>1,?:D;,@732eUUW5X34W0X13W2W4o"). Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j17Tg002dj11Tg003Bj12Tg0000j26Tg003ej13Tg005Ij25Tg00DZj24Tg00@Q#0R0#7#1%00#0R0#0#0#0#1#2R1'6%10#2#3\1R0%31f0,51'4X41X30W0X11W2o"). Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j1ITg002dj16Tg003Bj12Tg0000j2HTg003ej1CTg00;9j1<Tg00<:j35Tg00E4j27Tg00<]j24Tg005kj30Tg00E^j21Tg00FHj38Tg00Flj6GTg00GHj2FTg00Ggj1ETg00H@j3BTg00I8j4=Tg00ITj1>Tg00J4j2?Tg00JQj2@Tg000\j6ATg00=Rj5;Tg00K7j1:Tg00L6j2DTg00;Wj29Tg00@Q#3R0#IR1#6R2%30#3R0#3#3#3#6#2R3'H%60#2#C\3R0%22R4%31#<R1g00D>R5552R6f5R7f0R8'71476503X54P3f4R7/46R91776g00M4R:=525R;9046R4g00MRR<%28R=f1R>#2R?g00N0f2R@#2?0>8g00NKRAf3RB/1@11B>30[RC11@>11@850A%2B?0@>RD[117B117@50A\DA8@>8P>n2001000000120000000W3W2W4PC^3?^2=^4<P8P2P6P;P>O41126112;50APAP1PAp-0P8g00NiR;g00OFP;n011000003001000010000X6AP5P:P8EGP;1F;8b0b1b0W1%E4e9B76C=g00ObR6#>,?1,@2R4g00PAEAP7PBP@P>P8D;R8#:/74=039e1D86P51921d9521,47503eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j19Tg002dj17Tg003Bj13Tg0000j2JTg003ej1DTg00;9j18Tg00<:j35Tg00E4j24Tg00<]j26Tg005kj30Tg00E^j21Tg00FHj3:Tg00Flj6ITg00GHj2HTg00Ggj1GTg00H@j3CTg00I8j4BTg00Q;j1?Tg00ITj1>Tg00J4j2@Tg00JQj2ATg000\j6=Tg00=Rj5<Tg00K7j1ETg00L6j2;Tg00;Wj2FTg00@Q#2R0#9R1#7R2%20#2R0#2#2#2#7#3R3'J%70#3#D\3R0%32R4%91#8R5g00D>R6552R7f5R8f0R9'41687503X54P3f4R8/67R:1487g00M4R;=526R<9047R4g00MRR=%39R>f1R?#3R@g00N0f2RA#3?0?9g00NKRBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA:A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P2P7P<P?O41127112<50BPBP5PBp-0P9g00NiR<g00OFP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G4e9C87CB%21#8g00Ob#?R1#>'@,A2R7g00QZE=P8PCPAP?P9D<R9#E/47=03:e1;91P61F25d9525,68503eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j1:Tg002dj17Tg003Bj13Tg0000j2JTg003ej1DTg00;9j19Tg00<:j35Tg00E4j24Tg00<]j26Tg005kj30Tg00E^j22Tg00FHj3;Tg00Flj6ITg00GHj2HTg00Ggj1GTg00H@j3CTg00I8j4BTg00Q;j18Tg00ITj1?Tg00J4j2@Tg00JQj2ATg000\j6>Tg00=Rj5=Tg00K7j1ETg00L6j2<Tg00;Wj2FTg00@QR0#1R1#:R2#7R3%11#1R1#1#1#1#7#3R4'J%71#3#D\4R1%33R5%:0#1#1#9R0g00D>R6553R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00M4R;=536R<9057R5g00MRR=%39R>f1R?#3R@g00N0f2RA#3?0?9g00NKRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NiR<g00OFP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#9g00Ob#8#8R2#?'@,A3R7g00RTE>P8PCPAP?P9D=R9#E/47=04:e1<92P61F30d9530,68504eX;4X:1W7X84W9o"). Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00E^j20Tg00FHj37Tg001Zj15Tg002?j14Tg002dj1<Tg00;9j16Tg00Q;j13Tg00ITj1;Tg00J4j28Tg00JQj29Tg00<:j3:Tg00DZj2=Tg00MRR0f0R1#1R2f1R3#1R4g00N0f2R5#1?231g00NKR6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@QR1#5#4R0#<R2%50#6g00Ob#3#3#3#;'8,92%41#5#4#6g00D>5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00E^j20Tg00FHj37Tg001Zj15Tg002?j14Tg002dj1<Tg00;9j16Tg00Q;j13Tg00ITj1;Tg00J4j28Tg00JQj29Tg00<:j3:Tg00DZj2=Tg00MRR0f0R1#1R2f1R3#1R4g00N0f2R5#1?231g00NKR6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@QR1#5#4R0#<R2%50#6g00Ob#3#3#3#3#;'8,92%41#4#5#6g00D>5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj10Tg005kj33Tg00E^j22Tg00FHj37Tg001Zj16Tg002?j14Tg002dj1<Tg00;9j15Tg00Q;j11Tg00ITj1;Tg00J4j28Tg00JQj29Tg00<:j3:Tg00DZj2=Tg00MRR0f0R1#0R2f1R3#0R4g00N0f2R5#0?331g00NKR6f3R7/25127333R8[12531251536%07?353[R9f4#0?375\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00@QR1#6#4R0#<R2%60#5g00Ob#1#1#1#1#1#;'8,92%41#4#4#5g00D>5:2R11221,=6O4b3o"). Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j19Tg002dj15Tg003Bj13Tg0000j2JTg003ej1DTg00;9j1:Tg00<:j38Tg00E4j24Tg00<]j26Tg005kj30Tg00E^j22Tg00FHj3;Tg00Flj6ITg00GHj2HTg00Ggj1GTg00H@j3CTg00I8j4BTg00Q;j17Tg00ITj1?Tg00J4j2@Tg00JQj2ATg000\j6>Tg00=Rj5=Tg00K7j1ETg00L6j2<Tg00;Wj2FTg00@QR0#1R1#9R2#5R3%11#1R1#1#1#1#5#3R4'J%51#3#D\4R1%33R5%90#1#9#:R0g00D>R6583R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00M4R;=836R<9057R5g00MRR=%39R>f1R?#3R@g00N0f2RA#3?0?9g00NKRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NiR<g00OFP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#:g00Ob#7#7#7R2#?'@,A3R7g00SNE>P8PCPAP?P9D=R9#E/47=04:e1<92P61F30d9830,68504eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j19Tg002dj15Tg003Bj13Tg0000j2JTg003ej1DTg00;9j1:Tg00<:j38Tg00E4j26Tg00<]j27Tg005kj30Tg00E^j22Tg00FHj3;Tg00Flj6ITg00GHj2HTg00Ggj1GTg00H@j3CTg00I8j4BTg00Q;j14Tg00ITj1?Tg00J4j2@Tg00JQj2ATg000\j6>Tg00=Rj5=Tg00K7j1ETg00L6j2<Tg00;Wj2FTg00@QR0#1R1#9R2#5R3%11#1R1#1#1#1#5#3R4'J%51#3#D\4R1%33R5%90#9#1#:R0g00D>R6583R7f5R8f0R9'61787504X55P4f4R8/77R:1687g00M4R;=836R<9057R5g00MRR=%39R>f1R?#3R@g00N0f2RA#3?0?9g00NKRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NiR<g00OFP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%12#:g00Ob#4#4#4#4R2#?'@,A3R7g00TJE>P8PCPAP?P9D=R9#E/67=04:e1<92P61F30d9830,78504eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j15Tg002dj16Tg003Bj12Tg0000j2JTg003ej1DTg00;9j1:Tg00<:j38Tg00E4j29Tg00<]j27Tg005kj30Tg00E^j21Tg00FHj3;Tg00Flj6ITg00GHj2HTg00Ggj1GTg00H@j3CTg00I8j4BTg00Q;j14Tg00ITj1?Tg00J4j2@Tg00JQj2ATg000\j6>Tg00=Rj5=Tg00K7j1ETg00L6j2<Tg00;Wj2FTg00@QR0#3R1#5R2#6R3%31#3R1#3#3#3#6#2R4'J%61#2#D\4R1%23R5%50#5#5#:R0g00D>R6583R7f5R8f0R9'91787504X55P4f4R8/77R:1987g00M4R;=836R<9057R5g00MRR=%29R>f1R?#2R@g00N0f2RA#2?0?9g00NKRBf3RC/1A11C?30[RD11A?11A950B%2C?0A?RE[118C118A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41137113<50BPBP0PBp-0P9g00NiR<g00OFP<n011000003001000010000X6BP6P;P9EIP<1H<9b0b1b0W1%G5e9C87CB%32#:g00Ob#4#4#4#4#4R2#?'@,A3R7g00UFE>P8PCPAP?P9D=R9#E/97=04:e1<92P61F30d9830,78504eX;4X:1W7X84W9o"). Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h04addrh13memh22pch34regsh44segsh52x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00VBj24Tg00DZj25Tg00?R#8g00@Q#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1P0^01f4f1'4'5X51W1X21W3W4o"). Qed.

Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
  ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h04addrh13memh22pch34regsh43romh54segsh62x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00W5j24Tg00DZj25Tg00?R#8g00@Q#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1R2P0^01f5f2'4'5X61X42W1X21W3W5o"). Qed.

Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00DZj23Tg00@Q#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f2,30X41X30W0X11W2o"). Qed.

Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00DZj23Tg00@Q#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f1,30X41X30W0X11W2o"). Qed.

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch24regsh33romh41vh52x8p;1p;2p;7p;5p;3g001Zj10Tg002?j1ATg002dj11Tg003Bj12Tg0000j2@Tg003ej1:Tg005Ij28Tg00X2j75Tg00=Rj56Tg00Xij27Tg00Yij14Tg00;9j13Tg00;Wj29Tg00<:j3?Tg00Zfj3>Tg00[]j2;Tg009Hj5<Tg005kj3=Tg00@Q#0R0#AR1#1R2%00R0#0R3#0#0#0#1#2R4'@%13#2#:\4R3g00B6R5f5R6f4R7f1R8,84f3R9f2R:f0R;F5g00C7P6P7P9P:P8D6/7;#4P5%01#3R1g00D>1921d5?2=>6;%30,;7P9P:D<3=eX44X54X33W0X14W2o"). Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h03memh12pch21rh34regsh43romh52x8p;1p;2p;7p;5p;6p;3g001Zj10Tg002?j1DTg002dj13Tg003Bj14Tg0000j2CTg003ej1;Tg00\Tj7:Tg00=Rj58Tg001:j17Tg00]Oj22Tg00]oj11Tg00^Oj66Tg00_Mj29Tg00Yij1BTg00;9j15Tg00;Wj2ATg00<:j3<Tg00Zfj3=Tg00[]j2>Tg009Hj5?Tg005kj3@Tg00@Q#0R0#DR1#3R2%00R0#0R3#0#0#0#3#4R4'C%33#4R3#;\4R5g00B6R6f5R7f4R8f1R9f3R:f2R;f0R<F:g00C7P7P8P:P;P9D8P<%73,24#11244#1R3P3g00`F#1g00a>,24#1E6'9#BP6%01#5R1g00D>1A21d5<2==7<%50,>8P:P;D?3@eX24X54X45W0X14W3o"). Qed.

Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h01mh13memh22pch31rh45readsh54regsh63romh72x8p;1p;2p;5p;3p;6g001Zj10Tg002?j1GTg002dj13Tg003Bj14Tg0000j2FTg003ej1@Tg00]Oj22Tg001:j16Tg00=Rj5:Tg00Xij28Tg00Yij17Tg00;9j15Tg00<:j39Tg00Zfj3ETg00[]j2DTg009Hj5CTg005kj3?Tg00a]j6>Tg00]oj11Tg00^Oj6=Tg00b]j2ATg00_Mj2BTg00cXj3<Tg000\j6;Tg00@Q#0R0#GR1#3R2%00R0#0R3#0#0#0#3#4R4'F%33#4R3#@\4R5g00a>,24R6#6g00C7R7f6R8f5R9f4R:f3R;f2R<D:R=f1R>'8f0R?#7g00B6f7%01#5g00D>592;E<%50,D8P9P:DC5?7X07P8P9P:P;P<P>E>P>%63,24#11244#1R3P3g00`F#1%16E=,A?,B=A<=>?E;W4X34X74X65W1X24W5o"). Qed.

(* [comment removed for export] *)
Lemma rz_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

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
  intros segs regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hcnt Hn1 Hmax Hn64 Hrd Hc.
  pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
  eapply (rz_write_ch segs _ model fd ch (getr regs 17) bs T Hh Hlazy).
  - unfold fdchan. split; [exact Hlk | exact Hch].
  - apply fd32_id. exact Hfd32.
  - reflexivity.
  - exact Hno.
  - rewrite ms_gpr_epend0. exact Hfd.
  - rewrite ms_gpr_epend1, ms_gpr_epend2, Hcnt.
    rewrite (ms_read_bytes_rdn segs) by reflexivity. cbn [ms_mem epend].
    unfold word_to_nat. rewrite u64_lit by lia. rewrite Nat2Z.id. exact Hrd.
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
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) [] "h01Hh12H0h22Hah37__arithh44__ffh58__varmaph65__with74__x1h81zh96__sat0h:6__sat1h;2b1h<2b2h=1nh>2Hch?4codep;1p;2p;3p;4p;6p;7p;8g001Zj12Tg00;9j1:Tg00lhj20Tg00N0R0j26Tg003Bj18Tg005kj39Tg00E^j23Tg00FHj3NTg002dj1CTg00JQj2BTg002?j14Tg01cGj3aTg01clj2>Tg00lKj2HTg01dJj2ZTg01>3j2FTg01>[j3ETg00]oj1XTg001:j1WTg01??j2VTg01?]j1STg01@;j1RTg01AIj2QTg01@fj2;Tg00e[j1MTg01Alj3DTg01C:j2LTg00DZj2KTg01C\j2OTg01DHj3PTg01Dgj4JTg01djj3TTg01eMj1UTg01UCj1`Tg01ekj3_Tg000\j6?Tg01EYj2ITg01fNj3^Tg011<j2]Tg01BOj4GTg01V]j7[Tg01WAj7\Tg01Wej8YTg00M4R1f0R2']p=1g00NKR3f1R4;92p=7P3P4g01b4P2CGp==P4g01[FR5g01[eR6P6g01\ER7P2g01\eF[p=5P3P4g01Z_P2CGp=Af2R8P5P6P6P7P4P2F\p=@f3R9P5P6P6P7P8P4P2GYp=<%12g00@QR5#2R:#2#2R;#2#2#2R<#2#2#:R=,02R>'6g00MRR?%82R@%84RAP0%88?94213981394'7RB[13841382'7%89?984[RCf4RD#8?998\BAN842P2n2001000000120000000W<W;W=PC^<A^;@^=?P2%C<R?1B?8R@%45#4#4#4#4#4#4#:RA,B?RC5a?RBP@P313?@RE13?CRF'>1B?9,3?,72X83P3P81>2F/72X83P3PA1>92/79X83P3%::R:%:;RG'HRH,Z81729X831F:G101:RI%1GRJ101H[[%1:RKg00OFRLAE:G4UW2%1H\L^2KP0%1DRM10D=RDf5RN#1RO10NH'6P9f6#1RPf7/0=RQg01aHRR#XRS%WRRR1V34RT%S3RU%R3RV1Q35R51;3='=,5VRW%M6R6PV1;31RX/A5,5VRYP61;3:RZ%C;5D3,=5,5V9@VYC<C<1LV7R7P2P8g00A6R;g00AVR['K1O28=9;[dAP314CJR[b4b5b6X73%14R;%18R\108H'6[\>^73P2f9P4P8O3R]b3W1W0P4P2O2n2001000000120000000b9b:9T8H%UG,>8P0P\108=PJP410N=PSPR%`3R=PU1;3G,AX,5VP7P[b4b5b6PJP2b3W1X0MP4P2O2n20010000001200000009_8GE?PF%:<R<,F:RF%1<1H:<RG,01[\IRIAE:<4VLX2KR<%1G\L^2KRKP0PMPD%1A10AG'6RLP9PSPRP=PU1;3AR=,AX,5VAD3Z?RZ,==,5V5@VP7P[b4b5b6PLP2b3X1QX0PP4P2O2n2001000000120000000b9b:,IAE?PEPFPIP<PKP0PMPD10NG,6OP9PSPRPTPUPVPWP6PVPYP61=5Z,5V9@VYC<C<P7P[b4b5b6X73108G,6\\;\>^73P]b3X1QX0PP4P2O2n2001000000121000000b9b:,I8E?13?BA^?@CE?O4b0W>X?3o"). Qed.

Lemma rz_exit_lit : forall segs regs pc mem rom model code,
  m_halted model = None -> is_exit_no (getr regs 17) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model)
           (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
  intros segs regs pc mem rom model code Hh Hx8 Ha0 Hc.
  rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.
