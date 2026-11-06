(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk RefMemcpyLib S1MemcpyBase SumMemcpyBase SumMemcpy.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1Memcpy () := "I49OSSVerify5KrLib<S1MemcpyBase3mcH00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib=SumMemcpyBase3mcH00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2or00K49OSSVerify5KrLib=SumMemcpyBase3mcH01C1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib5Hoare6ret_okC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib9SumMemcpy9s1_memcpyC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3Drv8S1Memcpy7mcH_sumC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section ALL.
  Context {fx : FPState}.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HOK : S1MemcpyBase.mcH mem0 dst src n bs.

  Lemma mcH_sum : SumMemcpyBase.mcH RSEGS mem0 dst src n bs.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Memcpy ()) ["ALL"] "p'0h05Hdisji005Hdisjh14Hdsti014Hdsth24Hleni024Hlenh32Hni032Hnh44Hnwdi044Hnwdh54Hnwsi054Hnwsh64Hsrci064Hsrch71mp;5p;6p;2p;1p;3p;4p;=g0000R0j5ETg000gj6DTg001_j23Tg002;j10Tg002`j17Tg003>j2?Tg003[j22Tg0047j2;Tg004Rj14Tg0050j1:Tg005Sj28Tg0063j19Tg006Sj31Tg006mj1CTg007Mj1BTg007oj4@Tg008`j2>Tg009Bj4=Tg00:Bj26Tg00:lj25Tg00;Ij2<Tg00;cl=ATp,3HOKp,4mem0R1p,3dstR2p,3srcR3p,1nR4p,2bsR5DEP0P1P2P3P4P5g00<[R0P1P2P3P4P5EDf0R6g00>P/34g00>n#0R7#7%07#0R7#0#0#0R8#7'?R9,24';g00?S%47#:R7/85R:%9431%C7R7#BP0P1P3P:C@1>7531g00@2P0P1P2P:C=g00@R31%48R8/62R:/54R71683R8'31584R8/3:'<12891279P0P1P2P3P4P5f6R5f5R4f4R3f3R2f2R1f1R0P6M=AW4W5W0W1W6W2W3P5P4P3P2P1P0P6O7n5000001000000171103102106101100105104b7o"). Qed.

  Theorem ref_memcpy : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs s1_memcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
Proof.
ltac2:(KReplay.run1 (kr_t_S1Memcpy ()) ["ALL"] "h02H1h13H10h23H11h33H12h44Hreth54regsh63retp;1p;2p;3p;?g002;j10Tg00A2j15Tg004Rj16Tg0050j17Tg00AWj2;Tg00BCj1:Tg002`j13Tg00C4j32Tg00CWj21Tg006Sj34Tg00DIj28Tg00Dol?9Tg00>nR0#0R1#5R2#6R3%01#0#0#0#0#6R1#7R4';f0R5#:f2R6%30g00EgR7523'1f1R8544f3R9%02#3=237'1p,3dstR:544f4R;%52#3=237'1p,3srcR2544f5R<%50#0#0#3=237'1p,1nR7,81544p,2fxp,4mem0P:P2P7p,2bsp,3romf6P<g00FCP;P9P6P8P5M?9W3W2W1W0W4X64W5o"). Qed.
End ALL.
