(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: some recorded proofs replaced by tactic proofs; the channel-reader premise of writev; the BMode context; the model's access_ok checks. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AgentLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_AgentNodes () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:step_ecallC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes5ependC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7getr_nzC13~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9arg_reg_0C13~~~K47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9arg_reg_1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9arg_reg_2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes9arg_reg_3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes9arg_reg_4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes9arg_reg_5C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim3mrbC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec7adv_setC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FileSim;adv_eff_retC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01C4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectI4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00I47Corelib4Init9Datatypes3nat00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=adv_set_ependC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<with_copyinsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSimMapply_effect_copyins_no_writeC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes@step_ecall_ependC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_stepC13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:rdn_lengthC13~~~C47Corelib4Init9Datatypes6lengthK47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6fdchanC13~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall7fd32_idc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=ms_gpr_epend0C13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ms_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;word_to_natC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AgentLib7u64_litC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExecAms_read_bytes_rdnC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=ms_gpr_epend2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes=ms_gpr_epend1C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim;buf_modeledC13~~~C47Corelib5Lists7ListDef6firstnC4ELinuxProcessSemantics?LinuxProcessSem6BvBase8len_wordC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8min_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List=length_firstnK46Stdlib9micromega6VarMap1t01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SpinAlgX<srz_write_chC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minK46Stdlib9micromega=RingMicromega3Op201I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K47Corelib4Init9Datatypes4bool02C5ELinuxProcessSemantics?LinuxProcessSem3Sys7Uaccess<rw_bytes_maxI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01C45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC45stdpp9bitvector;definitions?bv_and_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ExitSim:is_exit_noC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8srz_exitC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:AgentNodes@bv_and_255_smallC13~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h03memh12pch24regsh33romh44segsh51wp;1p;2p;3p;9p;5g0000R0p4p7210p1000\p4p710p8g001:j1CTg001Zj10Tg002?j14Tg002dj11Tg003Bj13TP0j2<Tg003ej15Tg004Gj28Tg005Ij27Tg005kj32Tg006Ej16Tg007El99Tg008Sj1:Tg009[j5BTg00:cj2ATg00;_j1@Tg00<=j3=Tg00<`j2>Tg00=hj5?Tg00?3j2;Tg00@;#Cg00A:#0R0#4#1R1%00#0R0#0#0R2#0#1#3R3'<%10#3#5\3R4%12#3R2%52f5R5f3R6'8f0R7,7232g00A_f1R2#6g00B?32p,2fxR8f7R9f6R:P5f4R;P6f2P2P7M99g00B_R7#:P8P:P5P;P6DB,A9P:P5P;P6%40#@g00Cf5=1,>:D?,;732eUUW5X34W0X13W2W4o"). Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j17Tg002dj11Tg003Bj12Tg0000j26Tg003ej13Tg005Ij25Tg00DBj24Tg00A:#0R0#7#1%00#0R0#0#0#0#1#2R1'6%10#2#3\1R0%31f0,51'4X41X30W0X11W2o"). Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j1HTg002dj15Tg003Bj13Tg0000j2GTg003ej1<Tg00;_j1;Tg00<=j37Tg00D\j24Tg00<`j26Tg005kj30Tg00EFj21Tg00F0j38Tg00FTj6FTg00G0j2ETg00GOj1CTg00Ghj3=Tg00I3j4>Tg00IOj1?Tg00Ioj2@Tg00JLj2ATg000\j6BTg00=hj5:Tg00K2j19Tg00L1j2DTg00A:#2R0#HR1#5R2%20#2R0#2#2#2#5#3R3'G%50#3#<\3R0%32R4%21#;R1g00CfR5572R6f5R7f0R8'41676503X54P3f4R7/66R91476g00LoR:=725R;9046R4g00MMR<%38R=f1R>#3R?g00Mkf2R@#3?0>8g00NFRAf3RB/1@11B>30[RC11@>11@850A%3B?0@>RD[117B117@50A\DA8@>8P>n2001000000120000000W3W2W4PC^3?^2=^4<P8P2P6P;P>O41126112;50APAP1PAp-0P8g00NdR;g00OAP;n011000003001000010000X6AP5P:P8EFP;1E;8b0b1b0W1%C4e9=76C>g00O]R6#?,@1,A2R2g00P<EBP7PBP@P>P8D:R8#9/42=039e1D86=039eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j19Tg002dj15Tg003Bj13Tg0000j2ITg003ej1DTg00;_j17Tg00<=j38Tg00D\j24Tg00<`j26Tg005kj30Tg00EFj21Tg00F0j3:Tg00FTj6HTg00G0j2GTg00GOj1FTg00Ghj3CTg00I3j4BTg00QIj1?Tg00IOj1>Tg00Ioj2@Tg00JLj2ATg000\j6=Tg00=hj5<Tg00K2j1ETg00L1j2;Tg00A:#2R0#9R1#5R2%20#2R0#2#2#2#5#3R3'I%50#3#D\3R0%32R4%91#7R5g00CfR6582R7f5R8f0R9'41687503X54P3f4R8/67R:1487g00LoR;=826R<9047R4g00MMR=%39R>f1R?#3R@g00Mkf2RA#3?0?9g00NFRBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA:A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P2P7P<P?O41127112<50BPBP5PBp-0P9g00NdR5g00OAP5n011000003001000010000X6BP6P;P9EHP51G59b0b1b0W1%F4e9C87CB%21#7g00O]#?R1#>'@,A2R2g00QhE=P8PCPAP?P9D<R9#E/42=03:e1;91=03:eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj11Tg002?j1:Tg002dj15Tg003Bj13Tg0000j2ITg003ej1DTg00;_j17Tg00<=j38Tg00D\j24Tg00<`j26Tg005kj30Tg00EFj22Tg00F0j3;Tg00FTj6HTg00G0j2GTg00GOj1FTg00Ghj3CTg00I3j4BTg00QIj19Tg00IOj1?Tg00Ioj2@Tg00JLj2ATg000\j6>Tg00=hj5=Tg00K2j1ETg00L1j2<Tg00A:R0#1R1#:R2#5R3%11#1R1#1#1#1#5#3R4'I%51#3#D\4R1%33R5%:0#1#1#7R0g00CfR6583R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00LoR;=836R<9057R5g00MMR=%39R>f1R?#3R@g00Mkf2RA#3?0?9g00NFRBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00NdR0g00OAP0n011000003001000010000X6BP6P;P9EHP01G09b0b1b0W1%F5e9C87CB%12#7g00O]#9#9R2#?'@,A3R3g00S5E>P8PCPAP?P9D=R9#E/43=04:e1<92=04:eX;4X:1W7X84W9o"). Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00EFj20Tg00F0j37Tg001Zj15Tg002?j14Tg002dj1<Tg00;_j16Tg00QIj13Tg00IOj1;Tg00Ioj28Tg00JLj29Tg00<=j3:Tg00DBj2=Tg00MMR0f0R1#1R2f1R3#1R4g00Mkf2R5#1?231g00NFR6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00A:R1#5#4R0#<R2%50#6g00O]#3#3#3#;'8,92%41#5#4#6g00Cf5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj11Tg005kj32Tg00EFj20Tg00F0j37Tg001Zj15Tg002?j14Tg002dj1<Tg00;_j16Tg00QIj13Tg00IOj1;Tg00Ioj28Tg00JLj29Tg00<=j3:Tg00DBj2=Tg00MMR0f0R1#1R2f1R3#1R4g00Mkf2R5#1?231g00NFR6f3R7/05107332R8[10531051526%17?253[R9f4#1?275\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00A:R1#5#4R0#<R2%50#6g00O]#3#3#3#3#;'8,92%41#4#5#6g00Cf5:2R11021,=6O4b3o"). Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h02b1h12b2h21nh31Hp;1p;3p;2g003Bj10Tg005kj33Tg00EFj22Tg00F0j37Tg001Zj16Tg002?j14Tg002dj1<Tg00;_j15Tg00QIj11Tg00IOj1;Tg00Ioj28Tg00JLj29Tg00<=j3:Tg00DBj2=Tg00MMR0f0R1#0R2f1R3#0R4g00Mkf2R5#0?331g00NFR6f3R7/25127333R8[12531251536%07?353[R9f4#0?375\8A7531P1n2001000000120000000W1W0W2P9^14^02^20P1g00A:R1#6#4R0#<R2%60#5g00O]#1#1#1#1#1#;'8,92%41#4#4#5g00Cf5:2R11221,=6O4b3o"). Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j17Tg002dj15Tg003Bj13Tg0000j2ITg003ej1DTg00;_j19Tg00<=j3:Tg00D\j24Tg00<`j28Tg005kj30Tg00EFj21Tg00F0j3;Tg00FTj6HTg00G0j2GTg00GOj1FTg00Ghj3CTg00I3j4BTg00QIj16Tg00IOj1?Tg00Ioj2@Tg00JLj2ATg000\j6>Tg00=hj5=Tg00K2j1ETg00L1j2<Tg00A:R0#2R1#7R2#5R3%21#2R1#2#2#2#5#3R4'I%51#3#D\4R1%33R5%70#2#7#9R0g00CfR65:3R7f5R8f0R9'41887504X55P4f4R8/87R:1487g00LoR;=:36R<9057R5g00MMR=%39R>f1R?#3R@g00Mkf2RA#3?0?9g00NFRBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41137113<50BPBP0PBp-0P9g00NdR0g00OAP0n011000003001000010000X6BP6P;P9EHP01G09b0b1b0W1%F5e9C87CB%22#9g00O]#6#6#6R2#?'@,A3R3g00TBE>P8PCPAP?P9D=R9#E/43=04:e1<92=04:eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj12Tg002?j17Tg002dj15Tg003Bj13Tg0000j2ITg003ej1DTg00;_j19Tg00<=j3:Tg00D\j26Tg00<`j28Tg005kj30Tg00EFj21Tg00F0j3;Tg00FTj6HTg00G0j2GTg00GOj1FTg00Ghj3CTg00I3j4BTg00QIj14Tg00IOj1?Tg00Ioj2@Tg00JLj2ATg000\j6>Tg00=hj5=Tg00K2j1ETg00L1j2<Tg00A:R0#2R1#7R2#5R3%21#2R1#2#2#2#5#3R4'I%51#3#D\4R1%33R5%70#7#2#9R0g00CfR65:3R7f5R8f0R9'61887504X55P4f4R8/87R:1687g00LoR;=:36R<9057R5g00MMR=%39R>f1R?#3R@g00Mkf2RA#3?0?9g00NFRBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41137113<50BPBP0PBp-0P9g00NdR0g00OAP0n011000003001000010000X6BP6P;P9EHP01G09b0b1b0W1%F5e9C87CB%22#9g00O]#4#4#4#4R2#?'@,A3R3g00UQE>P8PCPAP?P9D=R9#E/63=04:e1<92=04:eX;4X:1W7X84W9o"). Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g001Zj13Tg002?j15Tg002dj16Tg003Bj12Tg0000j2ITg003ej1DTg00;_j19Tg00<=j3:Tg00D\j27Tg00<`j28Tg005kj30Tg00EFj21Tg00F0j3;Tg00FTj6HTg00G0j2GTg00GOj1FTg00Ghj3CTg00I3j4BTg00QIj14Tg00IOj1?Tg00Ioj2@Tg00JLj2ATg000\j6>Tg00=hj5=Tg00K2j1ETg00L1j2<Tg00A:R0#3R1#5R2#6R3%31#3R1#3#3#3#6#2R4'I%61#2#D\4R1%23R5%50#5#5#9R0g00CfR65:3R7f5R8f0R9'71887504X55P4f4R8/87R:1787g00LoR;=:36R<9057R5g00MMR=%29R>f1R?#2R@g00Mkf2RA#2?0?9g00NFRBf3RC/1A11C?30[RD11A?11A950B%2C?0A?RE[118C118A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41137113<50BPBP0PBp-0P9g00NdR0g00OAP0n011000003001000010000X6BP6P;P9EHP01G09b0b1b0W1%F5e9C87CB%32#9g00O]#4#4#4#4#4R2#?'@,A3R3g00V`E>P8PCPAP?P9D=R9#E/73=04:e1<92=04:eX;4X:1W7X84W9o"). Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h04addrh13memh22pch34regsh44segsh52x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00Woj24Tg00DBj25Tg00@;#8g00A:#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1P0^01f4f1'4'5X51W1X21W3W4o"). Qed.

Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
  ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h04addrh13memh22pch34regsh43romh54segsh62x8p;1p;2g001:j18Tg001Zj10Tg002?j13Tg002dj11Tg003Bj12Tg0000j27Tg003ej16Tg00Y5j24Tg00DBj25Tg00@;#8g00A:#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1R2P0^01f5f2'4'5X61X42W1X21W3W5o"). Qed.

Lemma ms_mem_epend : forall regs pc mem rom x8, ms_mem (epend regs pc mem rom x8) = mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00DBj23Tg00A:#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f2,30X41X30W0X11W2o"). Qed.

Lemma ms_rom_epend : forall regs pc mem rom x8, ms_rom (epend regs pc mem rom x8) = rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h03memh12pch24regsh33romh42x8p;1p;2g001Zj10Tg002?j16Tg002dj11Tg003Bj12Tg0000j25Tg003ej14Tg00DBj23Tg00A:#0R0#6#1%00#0R0#0#0#0#1#2R1'5%10#2#4\1R0f1,30X41X30W0X11W2o"). Qed.

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h03memh12pch24regsh33romh41vh52x8p;1p;2p;7p;5p;3g001Zj10Tg002?j1@Tg002dj11Tg003Bj12Tg0000j2?Tg003ej1:Tg005Ij28Tg00Z2j75Tg00=hj56Tg00[<j27Tg00\<j14Tg00;_j13Tg00<=j39Tg00]9j3>Tg00^Cj2=Tg009[j5;Tg005kj3<Tg00A:#0R0#@R1#1R2%00R0#0R3#0#0#0#1#2R4'?%13#2#:\4R3p,2fxR5f5R6f4R7f1R8,84f3R9f2R:f0R;F5g00B_P6P7P9P:P8D6/7;#4P5%01#3g00Cf592=>6;%30,=7P9P:D;3<eX44X54X33W0X14W2o"). Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h03memh12pch21rh34regsh43romh52x8p;1p;2p;7p;5p;6p;3g001Zj10Tg002?j1CTg002dj13Tg003Bj14Tg0000j2BTg003ej1;Tg00_Mj7:Tg00=hj58Tg001:j17Tg00`[j22Tg00a;j11Tg00a[j66Tg00bYj29Tg00\<j1ATg00;_j15Tg00<=j3@Tg00]9j3<Tg00^Cj2=Tg009[j5>Tg005kj3?Tg00A:#0R0#CR1#3R2%00R0#0R3#0#0#0#3#4R4'B%33#4R3#;\4R5p,2fxR6f5R7f4R8f1R9f3R:f2R;f0R<F:g00B_P7P8P:P;P9D8P<%73,24#11244#1R3P3g00cR#1g00dJ,24#1E6'9#AP6%01#5g00Cf5@2=<7<%50,=8P:P;D>3?eX24X54X45W0X14W3o"). Qed.

Lemma adv_eff_ret_copyins_epend : forall regs pc mem rom x8 r reads,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (with_copyins reads (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h01mh13memh22pch31rh45readsh54regsh63romh72x8p;1p;2p;5p;3p;6g001Zj10Tg002?j1GTg002dj13Tg003Bj14Tg0000j2FTg003ej1@Tg00`[j22Tg001:j16Tg00=hj5:Tg00[<j28Tg00\<j17Tg00;_j15Tg00<=j39Tg00]9j3ETg00^Cj2DTg009[j5CTg005kj3?Tg00dij6>Tg00a;j11Tg00a[j6=Tg00f<j2ATg00bYj2BTg00g7j3<Tg000\j6;Tg00A:#0R0#GR1#3R2%00R0#0R3#0#0#0#3#4R4'F%33#4R3#@\4R5g00dJ,24R6#6g00B_R7f6R8f5R9f4R:f3R;f2R<D:R=f1R>'8f0R?#7p,2fxf7%01#5g00Cf592;E<%50,D8P9P:DC5?7X07P8P9P:P;P<P>E>P>%63,24#11244#1R3P3g00cR#1%16E=,A?,B=A<=>?E;W4X34X74X65W1X24W5o"). Qed.

Lemma rz_sys : forall segs scfg regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h02HEh12HFh22Hch32Hhh45Hlazyh51Th63memh75modelh82pch94regsh:3romh;4scfgh<4segsh=1wp;1p;2p;3p;5p;8p;<g001:j18Tg001Zj10Tg002?j17Tg002dj11Tg003Bj14Tg0000j2CTg003ej13Tg00hVj1>Tg00iMj1<Tg005kj32Tg00`[j2;Tg00ioj1:Tg00a;j19Tg004Gj2ITg005Ij2HTg006Ej1GTg00;_j1BTg00<=j3@Tg00<`j25Tg00=hj56Tg00jgj2?Tg00k\j5ATg009[j5=Tg00DBj2DTg00lhj8ETg00n>l<FTg00@;#8g00oIg00A:#0R0#7#1R1%00#0R0#0#0R2#0#1#4R3'C%10#4#3\3R4g010C%12#4R2g0119%33R5f2R6#>%<3R7321;33R8#8f3R9#:%9832%32f:R8f7R:'I1H2932g00A_f4R2#Gg00B?32p,3bmKR;f<R<f;R=P8f9R>f8R?P:%70#Bg00Cf5@1R1,58D6f6R0'?P2DAP;f=R;P<p,2fxP=P8P>P?D=P:P=P8P>P?15=1D6f5P2P91D57P;P=P8P>P?P0P6f1GEf0M<FW2W0W1W4W3W5W=W7X:4W6X83W9W;W<o"). Qed.

Lemma rz_write_chan : forall segs scfg regs pc mem model fd ch n bs T,
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
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat k))) (v_addi pc 4) mem (seg_rom segs)) model) T) ->
  srealizes segs scfg (mkCfg (epend regs pc mem (seg_rom segs) (getr regs 17)) model)
           (t_write_ch ch bs T).
Proof.
  intros segs scfg regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hrdr Hcnt Hn1 Hmax Hn64 Hrd Hok Hc.
  pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
  eapply (srz_write_ch segs scfg _ model fd ch (getr regs 17) bs T Hh Hlazy).
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

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h01Hh12H0h22Hah37__arithh44__ffh58__varmaph65__with74__x1h81zh96__sat0h:6__sat1h;2b1h<2b2h=1nh>2Hch?4codep;1p;2p;3p;4p;6p;7p;8g001Zj12Tg00;_j1:Tg012^j20Tg00MkR0j26Tg003Bj18Tg005kj39Tg00EFj23Tg00F0j3NTg002dj1CTg00JLj2BTg002?j14Tg01lOj3aTg01m4j2>Tg012Aj2HTg01mRj2ZTg01EHj2FTg01F0j3ETg00a;j1XTg001:j1WTg01FTj2VTg01G2j1STg01GPj1RTg01H^j2QTg01H;j2;Tg00iMj1MTg01IAj3DTg01JOj2LTg00DBj2KTg01K1j2OTg01K]j3PTg01L<j4JTg01n2j3TTg01nUj1UTg01^7j1`Tg01o3j3_Tg000\j6?Tg01Lnj2ITg01oVj3^Tg0172j2]Tg01Idj4GTg01_ej7[Tg01`Ij7\Tg01`mj8YTg00LoR1f0R2']p=1g00NFR3f1R4;92p=7P3P4g01k<P2CGp==P4g01dNR5g01dmR6P6g01eMR7P2g01emF[p=5P3P4g01cgP2CGp=Af2R8P5P6P6P7P4P2F\p=@f3R9P5P6P6P7P8P4P2GYp=<%12g00A:R5#2R:#2#2R;#2#2#2R<#2#2#:R=,02R>'6g00MMR?%82R@%84RAP0%88?94213981394'7RB[13841382'7%89?984[RCf4RD#8?998\BAN842P2n2001000000120000000W<W;W=PC^<A^;@^=?P2%C<R?1B?8R@%45#4#4#4#4#4#4#:RA,B?RC5a?RBP@P313?@RE13?CRF'>1B?9,3?,72X83P3P81>2F/72X83P3PA1>92/79X83P3%::R:%:;RG'HRH,Z81729X831F:G101:RI%1GRJ101H[[%1:RKg00OARLAE:G4UW2%1H\L^2KP0%1DRM10D=RDf5RN#1RO10NH'6P9f6#1RPf7/0=RQg01jPRR#XRS%WRRR1V34RT%S3RU%R3RV1Q35R51;3='=,5VRW%M6R6PV1;31RX/A5,5VRYP61;3:RZ%C;5D3,=5,5V9@VYC<C<1LV7R7P2P8g00A_R;g00B?R['K1O28=9;[dAP314CJR[b4b5b6X73%14R;%18R\108H'6[\>^73P2f9P4P8O3R]b3W1W0P4P2O2n2001000000120000000b9b:9T8H%UG,>8P0P\108=PJP410N=PSPR%`3R=PU1;3G,AX,5VP7P[b4b5b6PJP2b3W1X0MP4P2O2n20010000001200000009_8GE?PF%:<R<,F:RF%1<1H:<RG,01[\IRIAE:<4VLX2KR<%1G\L^2KRKP0PMPD%1A10AG'6RLP9PSPRP=PU1;3AR=,AX,5VAD3Z?RZ,==,5V5@VP7P[b4b5b6PLP2b3X1QX0PP4P2O2n2001000000120000000b9b:,IAE?PEPFPIP<PKP0PMPD10NG,6OP9PSPRPTPUPVPWP6PVPYP61=5Z,5V9@VYC<C<P7P[b4b5b6X73108G,6\\;\>^73P]b3X1QX0PP4P2O2n2001000000121000000b9b:,I8E?13?BA^?@CE?O4b0W>X?3o"). Qed.

Lemma rz_exit_lit : forall segs scfg regs pc mem rom model code,
  m_halted model = None -> is_exit_no (getr regs 17) ->
  getr regs 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
  srealizes segs scfg (mkCfg (epend regs pc mem rom (getr regs 17)) model)
           (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FPX_1"] "h01bh13Ha0h22Hch32Hhh43Hx8h54codeh63memh75modelh82pch94regsh:3romh;4scfgh<4segsp;1p;2p;3p;5p;9p;6g001:j1NTg001Zj11Tg002?j10Tg002dj14Tg003Bj1>Tg0000j2JTg003ej1=Tg00hVj1BTg00iMj1@Tg005kj3<Tg00;_j13Tg00<=j37Tg00<`j22Tg020Dj1MTg00JLj25Tg0172j2LTg012^j2ITg00Mkj2HTg01lOj38Tg00=hj5;Tg00jgj2DTg021Qj1CTg022Dj2:Tg00k\j59Tg00L1j2ATg005Ij2ETg00DBj2FTg023Nl9GTg01=mj5?Tg00FTj66Tg024Yj2KTg00@;#Ng00oIg00A:R0#1R1#0R2#4R3%11#1R1#1#1#1R4#4R5#>R6'J%41#>#=\6R7g010Cg00NF%=6R8f1R9#B%@63<f6R:%01#3g00CfR1573R;'2#Mf7R<%12#3=731R1'2f2R3,555<6g00Lof3R2'L%14#1#3,I2'HP6f4R4,55R=%00#0#0#0#0#0#0#3,55R0585p,3bmKR>f<R?f;R@f:RAf9RBf8RCP<12A;D;/D:RDf0RE%C:RF':D9X06P612B1R1P>P?P@PDA85E0/:FD9X06RFP6PBPCP<P:12B;R;D;R0g00O]'APFP>P@PAP0f5P;P21E6;,F8P3M9GP1PBPCP<P:P;D?E6P=P9E6P=1K4EE6W2W1W4W3W5W7X:7W6X86W9W;W<o"). Qed.

End FPX_1.
