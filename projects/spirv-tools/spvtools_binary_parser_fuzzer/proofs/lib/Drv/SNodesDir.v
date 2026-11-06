(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  RelSpec SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes RefNodes SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_SNodesDir () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyK47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6to_natC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics?LinuxProcessSem5State9errno_retC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I49OSSVerify5KrLib9SRealizes9srealizes00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00C49OSSVerify5KrLib8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib6SNodes<srz_read_dirC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C49OSSVerify5KrLib8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00K4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry06C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC4ELinuxProcessSemantics?LinuxProcessSem5State6EISDIRI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma srz_read_dir_mapped : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  srealizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  srealizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_SNodesDir ()) ["WithSegs"] "h02Hah14__x1h23H12h33H17h43H64h52HEh62HFh72Hch83Hc1h93Hfdh:5Hfd32h;2Hhh<5Hlazyh=3Hlkh>3Hokh?5Hoverh@1KhA7__arithhB4__ffhC7__sat65hD7__sat66hE7__sat67hF7__sat68hG7__sat69hH7__sat70hI8__varmaphJ5__withK1bhL3cnthM2fdhN3memhO5modelhP2pchQ4regshR1whS1zp;1p;2p;3p;4p;5p;7p;6p;Cp;8g0000j11Tg000Uj14Tg001:j19Tg001Xj1>Tg002;j2mTg002gj1;Tg003Ij2]Tg004Kj2GTg004mj35Tg005Gj1XTg006Gj1NTg007>j1FTg007`j2lTg008@j1MTg008`j1fTg009Xj1JTg00:8j10Tg00:Vj3<Tg00;9j26Tg00;kj2ETg00<Qj28Tg00=;j2BTg00=Xj27Tg00>4j1ZTg00>hj2YTg00?`j23Tg00@<j2ATg00@Yj1WTg00A9j4VTg00B9j1UTg00C1j3TTg00Cej2STg00DYj1RTg00ENj5OTg00F@j2PTg00G5j3QTg00Goj2=Tg00HWj3@Tg00I;j2kTg00IYj1jTg00J7j1iTg00Jbj2gTg00KEj2DTg00Khj3HTg00LKj4KTg00M6j7aTg00MZj2`Tg00N<j2_Tg00NVj2bTg00OBj3cTg00Oaj4^Tg00PSj2dTg00Pnj2eTg00Qcj6LTg00RAlC\Tg00S9j7hTg00S]j8[Tg00TAR0f0R1g00TaR235p=?g00UAR3/31p=2g00U_R4f1R5g00V=P1CKp=CP5g00VdR6g00WCR7P7g00WcR8P1g00XCFhp=:f3R9P6P7P7P8f2R:P5P1G[p=Ig00XcR;#1R<#4R=#9R>%1<R?#1R@#1#1RA#1RB#9RC#>RD'm%9@#>#;\Dg00YH%9A#>REg00Z>%;Ep,4segsRFf6RG']1GE935f4#X#?%;D%NG%FD351lDDRE#Mf7R9#f%JE35f;RE%4@#0g00[0R@5<>'6%4;RH#4#4#4#4#0,EC55Df<RI%1=#0=<>@RJ'6=5D9f8RK,8C%0<R<%0ARA'BRL'7g00[LRM#;%ZEf9RN'Yg00\D,GM35f?RM%1H#1RH#0=<>@RO'61ECN55D%0;RPf:RQ'3%1HRH#0RR,B<RS,3EfBRT%4=#0=<>@R@'6,8C/AIg00]<R>'3PFfAR=fCRU/6@f=RV#WCV#?p,2fxRWfDRXg00^4#U7TJ%0?,SUPT%RFDO/P==QFVPWPFfERFPXPUPTP=f@f>PVPIPEPQPNPKP9PGPD1ECMRGfFR9/6@,8CR@18C1'A/3>XKDP4PM1A@1/3>XS4P:18CG1=<A173<RG%2A173L[[%2<R>g00^iR@A@<A5UW0%2L\@^0>%0BRB,=<%2B1B<BRL,73[\GA@<B5V@X0>%2L\@^0>1=<R%2R173S[\GA@<R5V@X0>%2S\@^0>g00_ER>#J%M>1k45%j4%i4R>1g4;R;1D4<R<%9H5H4'C,:>%F7RHP>1D4P/C;,:>PHP>P6P7P7P81D43/C;,:>P4P;g00`1AH4<CCK,:>FaCICI1`>8P1P:1_021b1:#?dAc435C^bBbIbJX14131S13P5%2:17:L'd[[^14P1P9PQPEO3bAbCbDbEbFbGbH,eMEL16FOf5ELP1MC\W7W>W?W4W8W2W=W:W9W3W<W;W5W6W@XL4XMDWRWOWNXPDWQo"). Qed.

End WithSegs.
