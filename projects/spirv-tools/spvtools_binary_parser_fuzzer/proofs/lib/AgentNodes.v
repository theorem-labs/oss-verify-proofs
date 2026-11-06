(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AgentLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AgentNodes () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec:step_ecallC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:AgentNodes5ependC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv3Sem7reg_getC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC49OSSVerify5KrLib8PropExec7getr_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_gprK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01C49OSSVerify5KrLib8PropExec9arg_reg_0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec9arg_reg_1C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9arg_reg_2C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7FileSim3mrbC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC49OSSVerify5KrLib7CatExec7adv_setC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8set_gpr0C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section FX. Context {fx : FPState}.
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
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "h03memh12pch24regsh33romh44segsh51wp;1p;2p;3p;9p;5g0000j1CTg000Pj10Tg0015j14Tg001Zj11Tg0028j13Tg002[j2<Tg003Gj15Tg003ij28Tg004kj27Tg005Mj32Tg005gj16Tg006gl99Tg007_j1:Tg008gj5BTg009Yj2ATg00:Uj1@Tg00;3j3=Tg00;Vj2>Tg00<Hj5?Tg00==j2;Tg00>E#Cg00?D#0R0#4#1R1%00#0R0#0#0R2#0#1#3R3'<%10#3#5\3R4%12#3R2%52f5R5f3R6'8f0R7,7232g00?if1R2#6g00@I32p,2fxR8f7R9f6R:P5f4R;P6f2P2P7M99g00@iR7#:P8P:P5P;P6DB,A9P:P5P;P6%40#@g00B05=1,>:D?,;732eUUW5X34W0X13W2W4o"). Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g000Pj12Tg0015j1HTg001Zj15Tg0028j13Tg002[j2GTg003Gj1<Tg00:Uj1;Tg00;3j37Tg00BLj24Tg00;Vj26Tg005Mj30Tg00C6j21Tg00C`j38Tg00DDj6FTg00D`j2ETg00E?j1CTg00EXj3=Tg00FMj4>Tg00Fij1?Tg00GIj2@Tg00Gfj2ATg00HLj6BTg00<Hj5:Tg00Hjj19Tg00Iij2DTg00?D#2R0#HR1#5R2%20#2R0#2#2#2#5#3R3'G%50#3#<\3R0%32R4%21#;R1g00B0R5572R6f5R7f0R8'41676503X54P3f4R7/66R91476g00JgR:=725R;9046R4g00KER<%38R=f1R>#3R?g00Kcf2R@#3?0>8g00L>RAf3RB/1@11B>30[RC11@>11@850A%3B?0@>RD[117B117@50A\DA8@>8P>n2001000000120000000W3W2W4PC^3?^2=^4<P8P2P6P;P>O41126112;50APAP1PAp-0P8g00L\R;g00M9P;n011000003001000010000X6AP5P:P8EFP;1E;8b0b1b0W1%C4e9=76C>g00MUR6#?,@1,A2R2g00N4EBP7PBP@P>P8D:R8#9/42=039e1D86=039eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g000Pj12Tg0015j19Tg001Zj15Tg0028j13Tg002[j2ITg003Gj1DTg00:Uj17Tg00;3j38Tg00BLj24Tg00;Vj26Tg005Mj30Tg00C6j21Tg00C`j3:Tg00DDj6HTg00D`j2GTg00E?j1FTg00EXj3CTg00FMj4BTg00Nkj1?Tg00Fij1>Tg00GIj2@Tg00Gfj2ATg00HLj6=Tg00<Hj5<Tg00Hjj1ETg00Iij2;Tg00?D#2R0#9R1#5R2%20#2R0#2#2#2#5#3R3'I%50#3#D\3R0%32R4%91#7R5g00B0R6582R7f5R8f0R9'41687503X54P3f4R8/67R:1487g00JgR;=826R<9047R4g00KER=%39R>f1R?#3R@g00Kcf2RA#3?0?9g00L>RBf3RC/1A11C?30[RD11A?11A950B%3C?0A?RE[118C118A50B\EA:A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P2P7P<P?O41127112<50BPBP5PBp-0P9g00L\R5g00M9P5n011000003001000010000X6BP6P;P9EHP51G59b0b1b0W1%F4e9C87CB%21#7g00MU#?R1#>'@,A2R2g00OJE=P8PCPAP?P9D<R9#E/42=03:e1;91=03:eX;3X:0W7X83W9o"). Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "p'0h01Hh12Hch22b1h32b2h41nh51bh61eh73memh82pch94regsh:3romh;2x8i001zp;1p;2p;3p;6p;4p;5g000Pj11Tg0015j1:Tg001Zj15Tg0028j13Tg002[j2ITg003Gj1DTg00:Uj17Tg00;3j38Tg00BLj24Tg00;Vj26Tg005Mj30Tg00C6j22Tg00C`j3;Tg00DDj6HTg00D`j2GTg00E?j1FTg00EXj3CTg00FMj4BTg00Nkj19Tg00Fij1?Tg00GIj2@Tg00Gfj2ATg00HLj6>Tg00<Hj5=Tg00Hjj1ETg00Iij2<Tg00?DR0#1R1#:R2#5R3%11#1R1#1#1#1#5#3R4'I%51#3#D\4R1%33R5%:0#1#1#7R0g00B0R6583R7f5R8f0R9'41687504X55P4f4R8/67R:1487g00JgR;=836R<9057R5g00KER=%39R>f1R?#3R@g00Kcf2RA#3?0?9g00L>RBf3RC/2A12C?30[RD12A?12A950B%3C?0A?RE[128C128A50B\EA;A?9P?n2001000000120000000W3W2W4PD^3@^2>^4=P9P3P7P<P?O41237123<50BPBP0PBp-0P9g00L\R0g00M9P0n011000003001000010000X6BP6P;P9EHP01G09b0b1b0W1%F5e9C87CB%12#7g00MU#9#9R2#?'@,A3R3g00PAE>P8PCPAP?P9D=R9#E/43=04:e1<92=04:eX;4X:1W7X84W9o"). Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "h04addrh13memh22pch34regsh44segsh52x8p;1p;2g0000j18Tg000Pj10Tg0015j13Tg001Zj11Tg0028j12Tg002[j27Tg003Gj16Tg00Q8j24Tg00Qhj25Tg00>E#8g00?D#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1P0^01f4f1'4'5X51W1X21W3W4o"). Qed.

Lemma ms_writable_byte_epend : forall segs regs pc mem rom x8,
  ms_writable_byte segs (epend regs pc mem rom x8) = wview segs mem.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "h04addrh13memh22pch34regsh43romh54segsh62x8p;1p;2g0000j18Tg000Pj10Tg0015j13Tg001Zj11Tg0028j12Tg002[j27Tg003Gj16Tg00RBj24Tg00Qhj25Tg00>E#8g00?D#0R0#3#1%00#0R0#0#0#0#1#2R1'7%10#2#6R0\1R2P0^01f5f2'4'5X61X42W1X21W3W5o"). Qed.

Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
ltac2:(KReplay.run1 (kr_t_AgentNodes ()) ["FX"] "h03memh12pch24regsh33romh41vh52x8p;1p;2p;7p;5p;3g000Pj10Tg0015j1@Tg001Zj11Tg0028j12Tg002[j2?Tg003Gj1:Tg004kj28Tg00S?j75Tg00<Hj56Tg00T3j27Tg00U3j14Tg00:Uj13Tg00;3j39Tg00V0j3>Tg00Vdj2=Tg008gj5;Tg005Mj3<Tg00?D#0R0#@R1#1R2%00R0#0R3#0#0#0#1#2R4'?%13#2#:\4R3p,2fxR5f5R6f4R7f1R8,84f3R9f2R:f0R;F5g00@iP6P7P9P:P8D6/7;#4P5%01#3g00B0592=>6;%30,=7P9P:D;3<eX44X54X33W0X14W2o"). Qed.

End FX.
