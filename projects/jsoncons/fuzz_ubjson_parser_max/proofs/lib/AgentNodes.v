(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AgentLib.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AgentNodes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AgentNodes.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1bool"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "3le"; "4Z"]; ["5Segment"; "6MachineOk"; "6fetch_word"; "6is_ecall"; "6machine_result"; "6machine_state"; "6ms_gpr"; "6ms_mem"; "6ms_read_byte"; "6ms_rom"; "6ms_svc_pending"; "6ms_writable_byte"; "6set_gpr0"; "6step"; "6wview"; "7SpuriousCfg"]; ["7advance_past_svc"; "7apply_effect"; "7mkCfg"; "8FdChannel"; "8FdEntry"; "8MemCopy"; "8Model"; "8fd_lookup"; "8m_fds"; "8m_fs"; "8m_halted"; "8m_vm_lazy"; "8mkEffectU"; "8with_copyins"; "9w_is0"; ":rw_bytes_max"]; [";bvmap"; "<epend"; "=is_exit_no"; ">mrb"; "?getr"; "?mkst"; "?rdn"; "?regupd"; "?seg_rom"; "?v_addi"; "@TSet"; "@t_exit"; "@t_write_ch"; "Asrealizes"; "Badd"; "Ble"]; ["Blt"; "Bof_nat"; "Bpow"; "0T"; "0addr"; "0bs"; "0ch"; "0code"; "0fd"; "0fx"; "0k"; "0mem"; "0model"; "0n"; "0pc"; "0r"]; ["0reads"; "0regs"; "0rom"; "0scfg"; "0segs"; "CBV"; "CZ_to_bv"; "Cbv"; "Cbv_and"; "Cbv_unsigned"; "0v"; "0w"; "0x8"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
(x8 : word) : machine_state :=
{| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |}.
Lemma step_ecall_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "QN'5'@%211&Q@y5'RGyR0%211%5241'8y8%611%311p061yQ0%:11'=%812&Br6r4%3221(2r1%2291%93841'3&Cr2%211(:%?3521'D'E%211&Mr8&QEvR9r7r5%4532F1E%7261(A&QA&QD(RE+A(;%33Q=21%52;1%75<Q0;O1%92C1%Q53C;1p0G1p0N1pUHQ91pU6Q<1pTHQ=1pTNQD1pU4QD1pU:QK1").
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.
Lemma epend_svc : ltac2:(TCodec.tc2 tcn__AgentNodes "N&Q@y5'RGyR0%211%5241'8y8%611%311p061'=%618&J&QAr5r4r3r2r1%6554321%811(2%12C4%=3<31pUJE1pU6@1pTHA1pTNH1pU4H1").
Proof. reflexivity. Qed.
Lemma ms_gpr_epend0 : ltac2:(TCodec.tc2 tcn__AgentNodes "Q2&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&F&QAr5r4r3r2r1%6554321(1%9221&QD(RE+:(;%33I21%52=1%A3H71pUJI1pU6D1pTHE1pTNL1pU4L1").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend1 : ltac2:(TCodec.tc2 tcn__AgentNodes "Q2&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&F&QAr5r4r3r2r1%6554321u1%9221&QD(RE+;(;%33I21%52=1%A3H71pUJI1pU6D1pTHE1pTNL1pU4L1").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend2 : ltac2:(TCodec.tc2 tcn__AgentNodes "Q2&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&F&QAr5r4r3r2r1%6554321u2%9221&QD(RE+<(;%33I21%52=1%A3H71pUJI1pU6D1pTHE1pTNL1pU4L1").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma arg_reg_3 : ltac2:(TCodec.tc2 tcn__AgentNodes "B'='RGy5%211&RF&QN+:&R1u3%211%5241%7291(RE+=(;%33=21/01=%A3>61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : ltac2:(TCodec.tc2 tcn__AgentNodes "B'='RGy5%211&RF&QN+:&R1u4%211%5241%7291(RE+>(;%33=21/01=%A3>61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : ltac2:(TCodec.tc2 tcn__AgentNodes "B'='RGy5%211&RF&QN+:&R1u5%211%5241%7291(RE+?(;%33=21/01=%A3>61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma ms_gpr_epend3 : ltac2:(TCodec.tc2 tcn__AgentNodes "Q2&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&F&QAr5r4r3r2r1%6554321u3%9221&QD(RE+=(;%33I21%52=1%A3H71pUJI1pU6D1pTHE1pTNL1pU4L1").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend4 : ltac2:(TCodec.tc2 tcn__AgentNodes "Q2&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&F&QAr5r4r3r2r1%6554321u4%9221&QD(RE+>(;%33I21%52=1%A3H71pUJI1pU6D1pTHE1pTNL1pU4L1").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend5 : ltac2:(TCodec.tc2 tcn__AgentNodes "Q2&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&F&QAr5r4r3r2r1%6554321u5%9221&QD(RE+?(;%33I21%52=1%A3H71pUJI1pU6D1pTHE1pTNL1pU4L1").
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_read_byte_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "Q3'5'@%211&Q@y5'RGyR0%211%5241'8y8%611%311p061'=pT:83&H&QAr4r3r2&QHr5%211r1%8576521%:11&QC%1268%?3>31pUJG1pTHB1pTNI1pU4I1pU:Q01").
Proof. reflexivity. Qed.
Lemma ms_writable_byte_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "Q3'5'@%211&Q@y5'RGyR0%211%5241'8y8%611%311p061'=pT:83&Kr6&QAr5r4r3r2r1%6554321%9281&N%12:6%>3=31pUJF1pU6A1pTHB1pTNI1pU4I1pU:Q01").
Proof. reflexivity. Qed.
Lemma ms_mem_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "K&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&G&QAr5r4r3r2r1%6554321%811%:3;15pUJB1pU6=1pTH>1pTNE1pU4E1").
Proof. reflexivity. Qed.
Lemma ms_rom_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "K&Q@y5'RGyR0%211%5241'8y8%611%311p061'=&I&QAr5r4r3r2r1%6554321%811%:3;14pUJB1pU6=1pTH>1pTNE1pU4E1").
Proof. reflexivity. Qed.
Lemma adv_set_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "Q<&Q@y5'RGyR0%211%5241'8y8%611%311p061'='E&Q0&L&QAr6r5r4r3r2%6554321r1%9221%;11&QEvR9&QG(RE+:(;%33N21%53@1:&QI+4%22B1%;5:41BA%J3I=1pUFQ21pUJQ31pU6N1pTHO1pTNQ61pU4Q61").
Proof. intros. unfold epend. apply adv_set. Qed.
Lemma adv_eff_ret_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "QK&Q@y5'RGyR0%211%5241'8y8%611%311p061'='E&Q0&Q1&QAr6r5r4r3r2%6554321(Q<r1(7'9'5%11C%32H1%511%52JJ%711'Q5%911'6%:2O1%<11%?6>86641%H2A1%J11&QEvR9&QG(RE+:(;%33Q=21%53O1H&QI+4%22Q11%;5:41Q1Q0%Q93Q8=1pU0QA1pUJQB1pU6Q=1pTHQ>1pTNQE1pU4QE1").
Proof. intros. unfold epend. apply adv_eff_ret. Qed.
Lemma adv_eff_ret_copyins_epend : ltac2:(TCodec.tc2 tcn__AgentNodes "R0&Q@y5'RGyR0%211%5241'8y8%611%311p061'5'9'6%22:1%411'='E&Q0&Q1&QAr7r6r5r4r3%6554321&Q=r1(Q<r2(7%E1H%E2M1%311%G2OO%511'Q5%711%81I%;6:64421%>2=1%G2@1%I11&QEvR9&QG(RE+:(;%33QA21%53N1E&QI+4%22Q01%;5:41Q0O%Q83Q7=1pU2Q:1pU0QF1pUJQG1pU6QB1pTHQC1pTNQJ1pU4QJ1").
Proof. intros. rewrite apply_effect_copyins_no_write. apply adv_set_epend. Qed.
Lemma rz_sys : ltac2:(TCodec.tc2 tcn__AgentNodes "RH'5'@%211'O&Q@y5'RGyR0%211%5241'8y8%611%311p061'Q6yQ0%;11&QJ'=%:1<&Q:r3%211(0%11A%73631'9%12DD%M11&Q;r4%211(7%116%@3631%J1C&Br;r8%3221(2%12I;%H3731'3&Cr5%211(:%N3521'QMr=r<(Q2&QAr:r9&QD(RE+A(;%33QH21%52H1%95I87H1r7%<221%@4?>1Dr>&QEvR9%251BQ0?>%B21Q0r6%G46F21p081p0J1p0Q11p0Q:1p0QD1pT8QM1pUHQO1pTJR21pU6R41pTHR51pTNR<1pU4R<1pU8RC1pU:RE1").
Proof.
intros segs scfg regs pc mem rom model w T Hh Hlazy HF HE Hc.
eapply srz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.
Lemma rz_write_chan : ltac2:(TCodec.tc2 tcn__AgentNodes "U?'5'@%211'O&Q@y5'RGyR0%211%5241'8y8%611%311p061'Q6'6%A15&QJ'=%:1<&Q:r6%211(0%11A%73631'9%12DD%M11&Q;r7%211(7%116%@3631'?&RI&QDr;(RE+A(;%33Q621%6251%82Q61+R0%L3;21r<+:%:3Q=18%=231r8%Q23Q=21&R0r9%C2QA1&R2+2+Q0%3221%7251'Q4%QE11&Q7&Q8%11Kr:%4221(2(Q3%11@%32:1%QF3:51'3&Q>%119(4%QK3421r@+<%Q93R<1Q7%Q<231&RF&R1%11B%32R?1%R43R?51'>u1%221QC&QO%81Q<&Q?%3221r=%<11%Q82Q7QC%Q<221%RI1RB&QFrFrBrD+;%R13S41QO%R4231r>%847621%Q82RL>%RK3;21r1%H2G1r2rA%K221'QMrJrI(Q2&QEvR9&QGrHr3%Q911%Q;2SG1%534R=1&QIrG+4%3221&QH%11@%>5=73Q11rE%A221%E4DC1QJp0G1p0K1pTFSL1&QA%:1C%S92Q:S4%35Q;9Q921rC%K221&QLr?%23Q31Q:%Q24KE41p0;1p0Q:1p0QG1p0QL1p0R11p0R51p0R?1p0RE1p0S21p0S;1p0SB1p0SO1p0T91pT8TB1pT<TD1pTLTF1pT>TO1pTBU01pTJTJ1pTHTL1pTNU31pU4U31pU8U:1pU:U<1").
Proof.
intros segs scfg regs pc mem model fd ch n bs T Hh Hlazy Hno Hfd Hfd32 Hlk Hch Hcnt Hn1 Hmax Hn64 Hrd Hc.
pose proof (rdn_length segs mem n (getr regs 11) bs Hrd) as Hlen.
eapply (srz_write_ch segs scfg _ model fd ch (getr regs 17) bs T Hh Hlazy).
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
Lemma bv_and_255_small : ltac2:(TCodec.tc2 tcn__AgentNodes "H'?'<&QOzr1%3221&R0+X0%2241%8241'='RGyR0%211&RH&RFr2%2251+WO%4271%63831%;3814p0=1pT@G1").
Proof.
intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma rz_exit_lit : ltac2:(TCodec.tc2 tcn__AgentNodes "RA'5'@%211'O&Q@y5'RGyR0%211%5241'8y8%611%311p061'Q6'?'=%81:&Q:r2%211(0%11?%73631&QB&QDr7(RE+A(;%33J21%6251%811r8+:%83O16%;231&RFr3%22Q11%H3Q141'<&QOzr4%3221&R0+X0%2241%8241'QMr<r;(Q2&QAr:r9%Q022K%4532IQ01r6%7221&QKr5%J2QI1&Q9%116%5231%A4@?71p0C1p0M1p0Q61p0Q@1pT@QI1pTJQK1pU6QM1pTHQN1pTNR51pU4R51pU8R<1pU:R>1").
Proof.
intros segs scfg regs pc mem rom model code Hh Hx8 Ha0 Hc.
rewrite <- (bv_and_255_small code Hc), <- Ha0, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply srz_exit; [exact Hh | reflexivity | exact Hx8].
Qed.
End FPX_1.
