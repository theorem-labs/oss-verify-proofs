(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ExitSim PropExec CatSim CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SeqExec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SeqExec.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SeqExec.WithFP4."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "2not"; "3add"; "3sub"; "4le"; "4lt"; "5firstn"; "5nth"; "5skipn"; "6N"; "6Z"; "7Z_to_le_bytes"; "7bytes_le_to_Z"; "7len_word"; "7nat_to_word"; "8Segment"]; ["9Build_machine_state"; "9MachineOk"; "9fetch_word"; "9is_ecall"; "9machine_result"; "9machine_state"; "9ms_read_bytes"; "9step"; "9store_ok"; "9word_to_le_bytes"; ":valid_argv"; ":valid_envp"; ";decode_any"; "<ALU_ADD"; "<ALU_AND"; "<ALU_OR"]; ["<ALU_SLL"; "<ALU_SLTU"; "<ALU_SRA"; "<ALU_SRL"; "<ALU_SUB"; "<ALU_XOR"; "<Auipc"; "<Jalr"; "<Load"; "<Lui"; "<M_DIVU"; "<M_MUL"; "<M_REMU"; "<Mul"; "<Op"; "<OpImm"]; ["<OpImm32"; "<SZ1"; "<SZ2"; "<SZ4"; "<SZ8"; "<ShiftImm"; "<Store"; "<instr"; "=bv_eqb"; "=bvmap"; ">low32"; ">mul_div"; ">reg_get"; "?cat_argv_ptr"; "?wbytes"; "@to_wexit"]; ["Ac_ltu"; "Afp_csr"; "Afp_regs"; "Agetr"; "Amkst"; "Ardn"; "Aregupd"; "Av_add"; "Av_addi"; "Av_addiw"; "Av_andi"; "Av_auipc"; "Av_lui"; "Av_mul"; "Av_ori"; "Av_slli"]; ["Av_sltiu"; "Av_srai"; "Av_srli"; "Av_sub"; "Av_subw"; "Av_xori"; "Bargv_layout_slack"; "Bv_jalr"; "Cv_divu"; "Cv_remu"; "Dadd"; "Ddiv"; "Dland"; "Dle"; "Dlor"; "Dlt"]; ["Dltb"; "Dmodulo"; "Dmul"; "Dof_N"; "Dof_nat"; "Dopp"; "Dpow"; "Dshiftl"; "Dsub"; "0a"; "0av"; "0b"; "0bs"; "0bs1"; "0bs2"; "0buf"]; ["0bufs"; "0c"; "0code"; "0d"; "0e"; "0ev"; "0fx"; "0imm"; "0j"; "0k"; "0l"; "0m"; "0mem"; "0n"; "0n1"; "0n2"]; ["0pc"; "0rd"; "0regs"; "0rom"; "0rs"; "0rs1"; "0rs2"; "0s"; "0segs"; "0sh"; "0sp"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_add"; "Ebv_and"]; ["Ebv_extract"; "Ebv_signed"; "Ebv_unsigned"; "Ebv_wrap"; "0tgt"; "0u"; "0v"; "0w"; "0x"; "0y"; "0z"]]).
Section WithFP1.
Context {fx : FPState}.
Definition v_jalr (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).
Lemma step_jal_link : forall segs regs pc mem rom w rd (imm : bv 21),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jal rd imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(btgt pc (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_addsext;
reflexivity.
Qed.
Lemma step_jalr : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(v_jalr (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 imm Hf He Hd.
exact (step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd).
Qed.
Lemma step_sd_val : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(R6(R4r3%342@E1+4%64=<21%I2<1%Q03<91&Q8r<&RH&RCr;%221@&U1%12Q:Q1%6231u8%:49Q821(=%Q=3Q321'Q4'Q5%211&Q7r=&RDvT6r:%352DA1QC%6251(Q1%F2DL&R>%G2IQG%E2QNQ@%J221&Q9%K2MQ9%22F1%73<41%?5>Q091QO%;2D1%R43D=1p0H1p0Q61p0QH1p0QO1pX@R:1pY>R=1pY<R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, b_npc4.
reflexivity.
Qed.
Lemma step_sd_at : ltac2:(TCodec.tc2 tcn__SeqExec "S9'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r;r9%3221(1r6%22<1%93841'3&Q3r7%211(5%?3521'<'R7'J%3221%N11&Q<r8%211(;(R6(R4r5%342@E1+4%64=<21%I2<1%Q03<91&RH&RCr=%221>&U1%12Q8O%6231%Q83QD1=r>%821D%Q;3QG1@&Q8r@u8%342<Q31(=%QA3Q721'Q4'Q5%211&Q7rA&RDvT6r?%352=1AG%6251(Q1%L24Q0&R>&Q9%12BQD%33HQ;1%;5:E51O%72@1%R43@91p0D1p0K1p0O1p0Q81p0QJ1p0R11pZ>RG1pWDRH1pX@R>1pY>RA1pY<RB1pZ@RD1pY8RG1pXJRH1pY2RO1pY6RO1pYBS61").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
rewrite (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv. reflexivity.
- rewrite Ha. exact Hok.
Qed.
Lemma step_addi_at : ltac2:(TCodec.tc2 tcn__SeqExec "S6'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(QO(Q=r4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&RH&RCr=%221E&U1%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC%H2FQ3%<5;2198%62A1%R33A81p0E1p0N1p0Q61p0QH1p0QO1pZ>RE1pX@R;1pY:R>1pY4R?1pZ@RA1pY8RD1pXJRE1pY2RL1pY6RL1pYBS31").
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_addi segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_add_at : ltac2:(TCodec.tc2 tcn__SeqExec "S4'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<'@%913&Q2r:r8%3221(1r5%22:1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%L11&Q<r7%211(;(QN(Q=r4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QB21%53QC@1%Q73M1I&RG&RCr=%221E%322Q0%5221%Q>3QH1Q7'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543?21%8271(Q1&RFr9%2381QB&RH%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pZ>RC1pY>R;1pY<R<1pY4R=1pZ@R?1pY8RB1pXJRC1pY2RJ1pY6RJ1pYBS11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_sub_at : ltac2:(TCodec.tc2 tcn__SeqExec "S4'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<'@%913&Q2r:r8%3221(1r5%22:1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%L11&Q<r7%211(;(QN(QDr4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QB21%53QC@1%Q73M1I&S3&RCr=%221E%322Q0%5221%Q>3QH1Q7'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543?21%8271(Q1&RFr9%2381QB&RH%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pZ>RC1pY>R;1pY<R<1pY4R=1pZ@R?1pY8RB1pXJRC1pY2RJ1pY6RJ1pYBS11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_lui_at : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<yD%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(QI%12>C+4%44;:21%G2:1%N3:71&R8(TKz(>%33QB21%53QC>1%Q53K1G&RL&SG&U1%12Q;C+<%4221%611%Q=3QI1Q1'Q4'Q5%211&Q7r>&RDvT6r=r<r;r:%6554321%9281(Q1&RFr8%2391Q8&RH%12:Q5%>5=31:9%72C1%R33C91p0G1p0Q01p0Q81p0QH1p0QO1pZ>RE1pX@R;1pY4R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof.
intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
rewrite (step_lui segs regs pc mem rom w rd imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_auipc_at : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<yD%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(QF%12>C+4%44;:21%G2:1%N3:71&R8(TKz(>%33QB21%53QC>1%Q53K1G&RKr;&SG&U1%12Q<D+<%4221%7261%Q>3QJ1Q2'Q4'Q5%211&Q7r>&RDvT6r=r<r:%55432B1%8271(Q1&RFr8%2381Q8&RH%129Q5%=5<31J9%72B1%R33B91p0F1p0Q01p0Q81p0QH1p0QO1pZ>RE1pX@R;1pY4R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof.
intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
rewrite (step_auipc segs regs pc mem rom w rd imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_addiw_at : ltac2:(TCodec.tc2 tcn__SeqExec "S6'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(R0r4%23?D1+4%54<;21%H2;1%O3;81&R8(TKz(>%33QC21%53QD?1%Q63L1H&RI&RCr=%221D&U1%12Q>Q0%6231%Q>3QJ1Q7'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QB&RH%12GQ4%=5<31:9%72B1%R33B91p0F1p0O1p0Q71p0QH1p0QO1pZ>RE1pX@R;1pY:R>1pY4R?1pZ@RA1pY8RD1pXJRE1pY2RL1pY6RL1pYBS31").
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_addiw segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_sltiu_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(QO(QAr4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&S0&RCr=%221E&U1%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pX@R<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_xori_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(QO(QEr4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&S5&RCr=%221E&U1%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pX@R<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_xori segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_mul_at : ltac2:(TCodec.tc2 tcn__SeqExec "S4'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<'@%913&Q2r:r8%3221(1r5%22:1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%L11&Q<r7%211(;(QM(QKr4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QB21%53QC@1%Q73M1I&RM&RCr=%221E%322Q0%5221%Q>3QH1Q7'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543?21%8271(Q1&RFr9%2381QB&RH%12FQ3%=5<31:9%72B1%R33B91p0F1p0N1p0Q61p0QH1p0QO1pZ>RC1pY>R;1pY<R<1pY4R=1pZ@R?1pY8RB1pXJRC1pY2RJ1pY6RJ1pYBS11").
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_andi_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(QO(Q>r4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&RJ&RCr=%221E&U1%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pX@R<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_ori_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(QO(Q?r4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&RN&RCr=%221E&U1%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pX@R<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
rewrite (step_ori segs regs pc mem rom w rd rs imm Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_slli_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y6%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(R5(Q@r4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&RO&RCr=%221E&U2%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pYDR<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
rewrite (step_slli segs regs pc mem rom w rd rs sh Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_srli_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y6%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(R5(QCr4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&S2&RCr=%221E&U2%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pYDR<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
rewrite (PropExec.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma step_srai_at : ltac2:(TCodec.tc2 tcn__SeqExec "S7'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y6%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(R5(QBr4%342@E1+4%64=<21%I2<1%Q03<91&R8(TKz(>%33QD21%53QE@1%Q73M1I&S1&RCr=%221E&U2%12Q?Q1%6231%Q?3QK1Q8'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543@21%8271(Q1&RFr9%2381QC&RH%12GQ4%=5<31:9%72B1%R43B91p0F1p0O1p0Q71p0QI1p0R01pZ>RF1pYDR<1pY:R?1pY4R@1pZ@RB1pY8RE1pXJRF1pY2RM1pY6RM1pYBS41").
Proof.
intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
rewrite (step_srai segs regs pc mem rom w rd rs sh Hf He Hd).
rewrite Hrd, Hv. reflexivity.
Qed.
Lemma rdn_wbytes_hit : ltac2:(TCodec.tc2 tcn__SeqExec "Q>'7'O%211'TMy8%211%611yR0%511':%115p031&S=&S:&U2r1%2291&SD&6r3%22?1%411%9261&SF+2+R0%3221%?251'@%D1G&REr5&R>r2r4%33@21%B2O2%746241(1%12Q15%<3;31p0>1pWDQ21pXHQ01pWJQ61pYBQ;1").
Proof.
intros segs bs. induction bs as [|b rest IH]; intros m a Hnw; [reflexivity|].
cbn [length] in Hnw |- *.
change (wbytes m a (b :: rest))
with (wbytes (fun x => if bv_eqb x a then Some b else m x) (a+1) rest).
set (m' := fun x : word => if bv_eqb x a then Some b else m x).
cbn [rdn].
destruct rest as [|b' rest'].
- cbn [wbytes rdn]. unfold m'. rewrite bv_eqb_refl. reflexivity.
- assert (Hu1 : bv_unsigned (a+1) = (bv_unsigned a + 1)%Z)
by (apply u_add1; cbn [length] in Hnw; lia).
assert (Hread : wbytes m' (a+1) (b' :: rest') a = Some b).
{ rewrite (wbytes_below (b' :: rest') m' (a+1) a);
[ unfold m'; rewrite bv_eqb_refl; reflexivity
| cbn [length] in *; lia
| pose proof (u64_range a); lia ]. }
rewrite Hread.
rewrite (IH m' (a+1)) by (cbn [length] in *; lia).
reflexivity.
Qed.
Lemma rdn_wbytes_hit8 : ltac2:(TCodec.tc2 tcn__SeqExec "Q<'7'O%211'TMyR0%211':y8%511%311p051&S=&S:&U2r2%22;1+8%5221&SF+2+R0%3221%;251'@%H1@%C11&REr5&R>r4r3&Q9u8%221C%63541%948153(1%12=4%?3=31p0A1pZ>Q31pWDQ41pXHQ01pYBQ91").
Proof.
intros segs m a v Hnw.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a) as H.
rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.
Lemma bytes_le_to_Z_8 : ltac2:(TCodec.tc2 tcn__SeqExec "?'TMyR0%211'@'J&L&Q9u8r1%3221%511&U2%12;4%:3931pZ><1").
Proof.
intro v. rewrite bytes_le_N.
change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
apply Z.mod_small. apply u64_range.
Qed.
Lemma c_ltu_ltb : ltac2:(TCodec.tc2 tcn__SeqExec "A'TMyR0%211'@'3&R@r2r1%3221&S@&U2%12:5%22;5%4221%;3:61pZD=1pZB>1").
Proof. reflexivity. Qed.
Lemma v_addiw_small : ltac2:(TCodec.tc2 tcn__SeqExec "Q5'TMyR0%211'J&S=z&S:&U2r2%2281r1%5221%8271&S?r3%82>1%:218&SF+2+O%3221%8251%B2A8'@&RIr5r4%3221%E2K1%F2L4%H214%83L31p0:1p0<1p0F1pX@Q01pZBQ21").
Proof.
intros x imm Hlo Hhi _. unfold v_addiw.
rewrite Z_to_bv_unsigned.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
Lemma v_addiw_id : ltac2:(TCodec.tc2 tcn__SeqExec "D'TMyR0%211&S?&U2r1%2251&SF+2+O%3221%8251'@&RIr2z%3221%53?13p071pZBA1").
Proof.
intros x Hx. apply bv_eq.
rewrite (v_addiw_small x 0); [lia | pose proof (u64_range x); lia .. ].
Qed.
Lemma land_255_small : ltac2:(TCodec.tc2 tcn__SeqExec "C'TMyR0%211&S?&U2r1%2251+X0%5221'@&TOr2&TL+WO%22=1%53>41%73>15p091pX4@1").
Proof.
intros c Hc. apply bv_eq.
rewrite bv_and_unsigned, Z_to_bv_unsigned.
change (bv_wrap 64 255) with (Z.ones 8).
rewrite Z.land_ones by lia.
apply Z.mod_small.
pose proof (u64_range c). change (2^8)%Z with 256%Z. lia.
Qed.
Lemma tw_write_ret : ltac2:(TCodec.tc2 tcn__SeqExec "SE'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061%>13%?11'@'J&U2&RCr7(TK+A(>%33D21%6251%82D1+R0%<3;21&R<r8+:%;3L19%4231&TL+1%22N1%E3N41%M1H&Q6(Q0r9&RBvT6%211(1%K25F%22Q81(0%11Q:&RA%118r6%=8<9G642Q11+;%Q23QC1Q0%K2?1+<%Q53QF1Q3%N2B1%E3741r5%A2Q@1%Q?3I31'Du1&6%12QH?%4231'8r1%7261r2%72QNQ0%:221'R?r?&RD&RFr>&M&Fr3r:%33R921%52R:1%837QF1&RHr=+4%3221r<r;%@5QB7321%C4B1QER0p0E1p0I1pXLL1%R?27R:%QF2RL1%QL89QH81QCQAAQK(4%13RHR8RB%L4?31QCp071p0Q51p0Q;1p0R61p0R@1pX6S61pX2RO1pX0S11pY8S31pXJS41pY2S;1pY6S;1pYBSB1").
Proof.
intros segs regs pc mem rom buf bufs code H17 H10 Hr Hnb Hcont.
eapply tw_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.
Lemma tw_exit_coden : ltac2:(TCodec.tc2 tcn__SeqExec "R5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061'@'J&U2&RCr5(TK+A(>%33B21%6251%82B1+RM%<3;21&R<r6+:%;3J19%4231r2%C3J21&S?r3%D2N1+X0%4221'R?r9(Q0r8&RBvT6%211r7(1%O26J%22Q:1(0%11Q<&RA%119%=8<98531JQ4(9%QH1Q=%211r4%D4C521p0F1p0L1p0Q41pX4QH1pY8QC1pXJQD1pY2QK1pY6QK1pYBR21").
Proof.
intros segs regs pc mem rom c H17 H10 Hc.
assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} 0)
(Z_to_bv 64 255) = c).
{ unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0, H10.
apply land_255_small. exact Hc. }
rewrite <- Hg.
eapply tw_exit.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
Qed.
Definition argv_layout_slack : Z := 4300000%Z.
Local Lemma argv_struct_arith : ltac2:(TCodec.tc2 tcn__SeqExec "Q2'J&S=zr2%3221r3+QP0%6221%7263r4+X0%:221&S:+8&SBr6+1%5221%4215%7261r5%9215%8219%;241+U0%=221+ZUH%J221p0A1p0E1p0G1p0K1pX:Q01pWDQ11").
Proof. intros. lia. Qed.
Local Lemma argv_sum_arith : ltac2:(TCodec.tc2 tcn__SeqExec "A'J&S=r2+ZUH%3221+RPPP0%5241&S:r4r3%3221+RPZUH%;221p071p0:1pWH?1pWD@1").
Proof. intros. lia. Qed.
Local Lemma argv_mod_arith : ltac2:(TCodec.tc2 tcn__SeqExec "N'J&S=zr2%3221r3+RPZUH%6221&S?&S:r5+TSWW0%3221&SF+2+R0%3221%9251'?r6%;21:%D2C1%>226%5221p071p0B1p0F1p0G1pXHL1pY@M1").
Proof. intros. lia. Qed.
Local Lemma argv_final_arith : ltac2:(TCodec.tc2 tcn__SeqExec "Q6'J&S=zr2%3221r4+RPZUH%6221+SooO%8241&S?&S:r7+TSWW0%3221&SF+2+R0%3221%9251'?r8%;21:%F221r6%>231+1%@221%B21:%9261p0;1p0F1p0I1p0M1p0N1pXFQ31pXHQ41pY@Q51").
Proof. intros. lia. Qed.
Lemma argv_ptr_bounds : ltac2:(TCodec.tc2 tcn__SeqExec "QL'TMyR0%211'7y8%511%311%411'8&Q:r3%211&Q;%113&E&6r5%22;1%4281&S?&S:&U2r7%22F1&S6%5221&SF+2+R0%3221%;251'?&S=r8%=2Q11&R=r6%244?1E%A2Q51%7251&SD&G(9%11Q6%34Q6LF1%N2Q81%611%K291+1%M221%O21E%D2<1p0F1p0Q31p0Q91p0Q<1pXDQ@1pX<QB1pWFQC1pYFQI1").
Proof.
intros sp av ev k Hva Hve Hk Hsp.
pose proof (valid_argv_len av Hva) as HavZ.
pose proof (valid_argv_str_len av k Hva Hk) as HnthZ.
destruct Hva as [Hlen [Htot [Hstr Hnz]]].
destruct Hve as [Helen _].
assert (HevZ : (Z.of_nat (length ev) <= 256)%Z) by exact Helen.
assert (HtotZ : (Z.of_nat (total_arg_bytes_nat (firstn k av)) <= 2097152)%Z).
{ rewrite total_arg_bytes_Z in Htot.
pose proof (total_arg_bytes_firstn_le k av). lia. }
assert (HA : (Z.of_nat (cat_struct_size av ev) <= 10424)%Z).
{ unfold cat_struct_size, auxv_size.
repeat (rewrite !Nat2Z.inj_add || rewrite !Nat2Z.inj_mul).
change (Z.of_nat 8) with 8%Z. change (Z.of_nat 1) with 1%Z.
change (Z.of_nat 160) with 160%Z.
apply argv_struct_arith;
solve [ exact HavZ | exact HevZ | apply Nat2Z.is_nonneg ]. }
assert (Hptr : cat_argv_ptr sp av ev k
= sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
rewrite nat_to_word_add_merge. reflexivity. }
set (n := (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))%nat) in *.
assert (HnZ : (Z.of_nat n <= 2107576)%Z)
by (unfold n; rewrite Nat2Z.inj_add; exact (argv_sum_arith _ _ HA HtotZ)).
assert (Hu : bv_unsigned (sp + nat_to_word n) = (bv_unsigned sp + Z.of_nat n)%Z).
{ unfold nat_to_word. rewrite bv_add_unsigned, Z_to_bv_unsigned.
rewrite bv_wrap_add_idemp_r, bv_wrap64_mod.
apply Z.mod_small.
pose proof (u64_range sp) as Hu64.
unfold argv_layout_slack in Hsp.
exact (argv_mod_arith _ _ (proj1 Hu64) (Nat2Z.is_nonneg n) HnZ Hsp). }
rewrite Hptr, Hu.
unfold argv_layout_slack in Hsp.
exact (argv_final_arith _ _ _ (Nat2Z.is_nonneg n)
(Nat2Z.is_nonneg (length (nth k av []))) HnZ HnthZ Hsp).
Qed.
Lemma step_jalr_x0 : ltac2:(TCodec.tc2 tcn__SeqExec "RJ'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(QG(TKz(>%33Q<21%531BG+4%84?>21%K2>1%Q23>;1&RCr;%221?%Q63QB1O'Q4'Q5%211&Q7r=&RDvT6r<r:%4532<1Q=%7261(Q1&S7&U1%12QGO%32Q:1%;5:918QD%62@1%QI3@81p0D1p0I1p0Q=1p0QD1pZ:R:1pX@R01pY<R31pZ@R51pY8R81pXJR91pY2R@1pY6R@1pYBRG1").
Proof.
intros segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht.
rewrite (step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd).
rewrite Ht. reflexivity.
Qed.
Lemma step_jalr_link : ltac2:(TCodec.tc2 tcn__SeqExec "S6'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r:r8%3221(1r5%22<1%93841'3&Q3r6%211(5%?3521'<'R7'J%3221%N11&Q<r7%211(;(QGr4%23?D1+4%54<;21%H2;1%O3;81&R8(TKz(>%33QC21%53QD?1%Q63L1H&RCr=%221C%Q:3QF1Q3'Q4'Q5%211&Q7r?&RDvT6r>r<r;%5543=21%8271(Q1&RFr9&RH%12CO%43:31&S7&U1%12R1Q9%32QD1%A5@51>=%;2F1%R33F=1p0J1p0O1p0Q71p0QH1p0QO1pZ:RE1pX@R;1pY<R>1pY4R?1pZ@RA1pY8RD1pXJRE1pY2RL1pY6RL1pYBS31").
Proof.
intros segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht.
rewrite (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd).
rewrite Ht, Hrd. reflexivity.
Qed.
Lemma getr_zero : ltac2:(TCodec.tc2 tcn__SeqExec "B&R9y5'TMyR0%211%5241'@&RCr1(TKz(>%33;21%6251&TL%12<5%:3<31pY6<1").
Proof. reflexivity. Qed.
End WithFP1.
Ltac reg_neq_tac :=
let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.
Section WithFP2.
Context {fx : FPState}.
End WithFP2.
Ltac getr_resolve :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero;
rewrite ?getr_nz by reg_neq_tac.
Section WithFP3.
Context {fx : FPState}.
End WithFP3.
Ltac regupd_resolve :=
repeat first [ rewrite regupd_same
| rewrite regupd_other by reg_neq_tac ].
Section WithFP4.
Context {fx : FPState}.
Goal forall regs (v : word), getr (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), getr (regupd regs 8 v) 0 = Z_to_bv 64 0.
Proof. intros. getr_resolve. reflexivity. Abort.
Goal forall regs (v : word), reg_get (regupd (regupd regs 8 v) 9 v) 8 = v.
Proof. intros. regupd_resolve. reflexivity. Abort.
Definition v_divu (x y : word) : word :=
Z_to_bv 64 (bv_unsigned x / bv_unsigned y).
Definition v_remu (x y : word) : word :=
Z_to_bv 64 (bv_unsigned x mod bv_unsigned y).
Lemma m_divu : ltac2:(TCodec.tc2 tcn__SeqExec "G'TMyR0%211&A'@'J&U2r1%2271z%63521%811&R;(QJr3r2%44?321&S8%1243%?3A31p091pWHC1pWDD1").
Proof.
intros a b Hb.
change (mul_div M_DIVU a b)
with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
rewrite (proj2 (Z.eqb_neq _ _) Hb).
apply bv_eq. unfold v_divu.
rewrite bv_divu_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range a). pose proof (u64_range b).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned a); [|lia].
apply Z.div_le_upper_bound; nia.
Qed.
Lemma m_remu : ltac2:(TCodec.tc2 tcn__SeqExec "G'TMyR0%211&A'@'J&U2r1%2271z%63521%811&R;(QLr3r2%44?321&S9%1243%?3A31p091pWHC1pWDD1").
Proof.
intros a b Hb.
change (mul_div M_REMU a b)
with (if (bv_unsigned b =? 0)%Z then a else bv_modu a b).
rewrite (proj2 (Z.eqb_neq _ _) Hb).
apply bv_eq. unfold v_remu.
rewrite bv_modu_unsigned, Z_to_bv_unsigned.
symmetry; apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range a). pose proof (u64_range b).
pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
lia.
Qed.
Lemma step_divu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs2) <> 0)%Z ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
erewrite step_mul_gen by eassumption.
rewrite m_divu by exact Hnz. reflexivity.
Qed.
Lemma step_remu : forall segs regs pc mem rom w rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_REMU rd rs1 rs2, 4%Z) ->
(bv_unsigned (getr regs rs2) <> 0)%Z ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
erewrite step_mul_gen by eassumption.
rewrite m_remu by exact Hnz. reflexivity.
Qed.
Lemma step_lw_zero : ltac2:(TCodec.tc2 tcn__SeqExec "SF'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(QH(R3(=r3%4532AF1+4%74>=21%J2=1%Q13=:1&R8(TKz(>%33QE21%53QFA1%Q83N1J%QL1QA%QD11&REr=r:&RH&RCr<%221K&U1%12QEQ7%6231u4%;4:921(4&TL%12R2E(9%11R3%53R431%63R541%73R651%83R761%QJ2G1%R13G;1'Q4'Q5%211&Q7r>&RDvT6r;%352NJ1M%6251(Q1&RFr8%G2RLQ;%33Q421%Q32Q1QC%;5:219Q5%72@1%RD3@91p0D1p0Q>1p0QF1p0R91p0R@1pX@RK1pY:RN1pY4RO1pZ@S11pY8S41pXJS51pY2S<1pY6S<1pYBSC1").
Proof.
intros segs regs pc mem rom w rd rs imm Hf He Hd Hrd Hr.
assert (Hval : sext 64 (bv_extract 0 32 (le_bytes_to_word
[Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]))
= Z_to_bv 64 0)
by (apply bv_eq; reflexivity).
step_pipeline Hf He Hd.
rewrite bv_eqb0_is_x0 in Hrd.
unfold getr in Hr; rewrite ?bv_eqb0_is_x0 in Hr.
rewrite ov_rdn, b_addsext, Hr; cbv beta iota.
rewrite Hval, Hrd; cbv beta iota.
rewrite b_npc4. reflexivity.
Qed.
Lemma step_sb : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(R6(R1r3%342@E1+4%64=<21%I2<1%Q03<91&Q8r<&RH&RCr;%221@&U1%12Q:Q1%6231u1%:49Q821(=%Q=3Q321'Q4'Q5%211&Q7r=&RDvT6r:%352DA1QC%6251(Q1%F2DL&R>%G2IQG%E2QNQ@%J221&Q9%K2MQ9%22F1%73<41%?5>Q091QO%;2D1%R43D=1p0H1p0Q61p0QH1p0QO1pX@R:1pY>R=1pY<R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
assert (Hsb : forall u : word,
Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
{ intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_wrap. lia. }
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, Hsb, b_npc4.
reflexivity.
Qed.
Lemma step_sb256 : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(R6(R1r3%342@E1+4%64=<21%I2<1%Q03<91&Q8r<&RH&RCr;%221@&U1%12Q:Q1%6231u1%:49Q821(=%Q=3Q321'Q4'Q5%211&Q7r=&RDvT6r:%352DA1QC%6251(Q1%F2DL&R>%G2IQG%E2QNQ@%J221&Q9%K2MQ9%22F1%73<41%?5>Q091QO%;2D1%R43D=1p0H1p0Q61p0QH1p0QO1pX@R:1pY>R=1pY<R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof. exact step_sb. Qed.
Lemma N_to_le_bytes_1_small : ltac2:(TCodec.tc2 tcn__SeqExec "F'TMyR0%211'@'7y8%611%311&Q9u1r1%3221(4&TL&U2%12>5%32;1(9%11<%73=31%A3=91pZ>C1").
Proof. reflexivity. Qed.
Lemma Zmod_pow2_div8 : ltac2:(TCodec.tc2 tcn__SeqExec "I'J&S=+8r1%3221'@&S;&SAr3&SF+2r2%3221%6251%524<%9221%:282&SH%127@%:291%=241%@3E61p0B1pXHG1pZFH1").
Proof.
intros z m Hm.
rewrite <- !Z.shiftr_div_pow2 by lia.
apply Z.bits_inj'; intros i Hi.
rewrite !Z.shiftr_spec by lia.
destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia.
rewrite Z.shiftr_spec by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_wrap : ltac2:(TCodec.tc2 tcn__SeqExec "O'8'I'J&S=&SB+8&SDr3%211%5241&SCr2%211%:241'@'7'TMy8%211%411&Kr4&U3%12@<%4231%524>%<3721p0>1pZFJ1pXHL1pXLN1").
Proof.
induction n as [|n IH]; intros m z Hm; cbn [Z_to_le_bytes]; [reflexivity|].
f_equal.
- apply bv_eq. rewrite !Z_to_bv_unsigned.
apply bv_wrap_bv_wrap. lia.
- replace (Z.shiftr (bv_wrap m z) 8) with (bv_wrap (m - 8) (Z.shiftr z 8)).
+ apply IH. lia.
+ unfold bv_wrap, bv_modulus.
rewrite !Z.shiftr_div_pow2 by lia.
rewrite Zmod_pow2_div8 by lia.
do 2 f_equal. lia.
Qed.
Lemma store_bytes_low16 : ltac2:(TCodec.tc2 tcn__SeqExec "F'TMyR0%211'@'7y8%611%311&Ku2&U2y@&U0wr1%34>241%6251%9281&Q9%12:5%A3=31pZ<C1").
Proof.
intro u. unfold word_to_le_bytes.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply Z_to_le_bytes_wrap. lia.
Qed.
Lemma store_bytes_low32 : ltac2:(TCodec.tc2 tcn__SeqExec "E'TMyR0%211'@'7y8%611%311&Ku4&U2yQ0&R:r1%211%5241%8271&Q9%1295%@3<31pZ<B1").
Proof.
intro u. unfold low32, word_to_le_bytes.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply Z_to_le_bytes_wrap. lia.
Qed.
Lemma step_sw_val : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(R6(R3r3%342@E1+4%64=<21%I2<1%Q03<91&Q8r<&RH&RCr;%221@&U1%12Q:Q1%6231u4%:49Q821(=%Q=3Q321'Q4'Q5%211&Q7r=&RDvT6r:%352DA1QC%6251(Q1%F2DL&R>%G2IQG%E2QNQ@%J221&Q9%K2MQ9%22F1%73<41%?5>Q091QO%;2D1%R43D=1p0H1p0Q61p0QH1p0QO1pX@R:1pY>R=1pY<R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
reflexivity.
Qed.
Lemma step_sw_at : ltac2:(TCodec.tc2 tcn__SeqExec "S9'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r;r9%3221(1r6%22<1%93841'3&Q3r7%211(5%?3521'<'R7'J%3221%N11&Q<r8%211(;(R6(R3r5%342@E1+4%64=<21%I2<1%Q03<91&RH&RCr=%221>&U1%12Q8O%6231%Q83QD1=r>%821D%Q;3QG1@&Q8r@u4%342<Q31(=%QA3Q721'Q4'Q5%211&Q7rA&RDvT6r?%352=1AG%6251(Q1%L24Q0&R>&Q9%12BQD%33HQ;1%;5:E51O%72@1%R43@91p0D1p0K1p0O1p0Q81p0QJ1p0R11pZ>RG1pWDRH1pX@R>1pY>RA1pY<RB1pZ@RD1pY8RG1pXJRH1pY2RO1pY6RO1pYBS61").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv. reflexivity.
- rewrite Ha. exact Hok.
Qed.
Lemma step_sh_val : ltac2:(TCodec.tc2 tcn__SeqExec "S5'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r9r7%3221(1r4%22<1%93841'3&Q3r5%211(5%?3521'<'R7'J%3221%N11&Q<r6%211(;(R6(R2r3%342@E1+4%64=<21%I2<1%Q03<91&Q8r<&RH&RCr;%221@&U1%12Q:Q1%6231u2%:49Q821(=%Q=3Q321'Q4'Q5%211&Q7r=&RDvT6r:%352DA1QC%6251(Q1%F2DL&R>%G2IQG%E2QNQ@%J221&Q9%K2MQ9%22F1%73<41%?5>Q091QO%;2D1%R43D=1p0H1p0Q61p0QH1p0QO1pX@R:1pY>R=1pY<R>1pZ@R@1pY8RC1pXJRD1pY2RK1pY6RK1pYBS21").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
step_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
rewrite b_addsext.
rewrite Hok; cbv beta iota.
rewrite write_to_mem_wbytes, store_bytes_low16, b_npc4.
reflexivity.
Qed.
Lemma step_sh_at : ltac2:(TCodec.tc2 tcn__SeqExec "S9'7'O%211&R9y5'TMyR0%211%5241':y8%611%311p061yQ0%:11%;1<y<%=11'@%;15&Q2r;r9%3221(1r6%22<1%93841'3&Q3r7%211(5%?3521'<'R7'J%3221%N11&Q<r8%211(;(R6(R2r5%342@E1+4%64=<21%I2<1%Q03<91&RH&RCr=%221>&U1%12Q8O%6231%Q83QD1=r>%821D%Q;3QG1@&Q8r@u2%342<Q31(=%QA3Q721'Q4'Q5%211&Q7rA&RDvT6r?%352=1AG%6251(Q1%L24Q0&R>&Q9%12BQD%33HQ;1%;5:E51O%72@1%R43@91p0D1p0K1p0O1p0Q81p0QJ1p0R11pZ>RG1pWDRH1pX@R>1pY>RA1pY<RB1pZ@RD1pY8RG1pXJRH1pY2RO1pY6RO1pYBS61").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
rewrite (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv. reflexivity.
- rewrite Ha. exact Hok.
Qed.
Lemma v_divu_small : ltac2:(TCodec.tc2 tcn__SeqExec "H'TMyR0%211&S?z&U2r1%2261%5241'@'J&S8r3r2%3221%:2>1&S;%<2@5%=2A5%3221%;3:51p0=1pZDD1pZBE1").
Proof.
intros x y Hy. unfold v_divu.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range x). pose proof (u64_range y).
split; [apply Z.div_pos; lia|].
apply Z.le_lt_trans with (bv_unsigned x); [|lia].
apply Z.div_le_upper_bound; nia.
Qed.
Lemma v_remu_small : ltac2:(TCodec.tc2 tcn__SeqExec "H'TMyR0%211&S?z&U2r1%2261%5241'@'J&S9r3r2%3221%:2>1&SA%<2@5%=2A5%3221%;3:51p0=1pZDD1pZBE1").
Proof.
intros x y Hy. unfold v_remu.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 64) with (2^64)%Z.
pose proof (u64_range y).
pose proof (Z.mod_pos_bound (bv_unsigned x) (bv_unsigned y) Hy).
lia.
Qed.
Lemma v_subw_small : ltac2:(TCodec.tc2 tcn__SeqExec "Q1'TMyR0%211&S=&U2r1%2251r2%4271%6231&S?&SHr3%92<1%3216&SF+2+O%3221%9251'@'J&S4r4%221<%E2H1%F2I3%@21>%83731p0:1p0E1pZDM1pZBN1").
Proof.
intros x y Hle Hlt. unfold v_subw.
rewrite Z_to_bv_unsigned.
rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.
Lemma land_d48 : ltac2:(TCodec.tc2 tcn__SeqExec "B'J&S=zr1%3221&S?r2+@%3221'@&S<r3+Q@%3221%53>1<p071p0<1pX8A1").
Proof.
intros d Hd0 Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 4) as [Hi4|Hi4].
- replace 48%Z with (Z.shiftl 3 4)%Z by reflexivity.
rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
- rewrite (Z_testbit_high 4 d i) by lia. reflexivity.
Qed.
Lemma lor_small_add : ltac2:(TCodec.tc2 tcn__SeqExec "D'J&S=zr1%3221&S?r2+@%3221'@&S>r3+Q@%3221&S:%1243%73@31p091p0>1pX8C1").
Proof.
intros d Hd0 Hd.
rewrite <- Z.lxor_lor by (apply land_d48; assumption).
rewrite <- Z.add_nocarry_lxor by (apply land_d48; assumption).
reflexivity.
Qed.
Lemma v_ori_lor : ltac2:(TCodec.tc2 tcn__SeqExec "F'TMyR0%211&S?&U2r1%2251+@%5221'@&RNr2+Q@%3221&TL&S:%<2?5%2215%42A1%:3A61p0<1pX8C1").
Proof.
intros d Hd. unfold v_ori.
change (bv_wrap 64 48) with 48%Z.
f_equal. apply lor_small_add; [apply u64_range | exact Hd].
Qed.
Lemma rdn_app : ltac2:(TCodec.tc2 tcn__SeqExec "QB'7'O%211'TMyR0%211':y8%511%311p051'8%<14'@%812&REr7r6r3r5%544321(1r2%22;1%;3:41r8&TNr4&N%11<%43J31%@46?1<%C3B19r9&B%12CB%E43;A1&2%13N;D%B2K1%K3J41p091p0B1pWNO1pWLQ01pWDQ81pY0Q31pXNQ41pXJQ61pYBQ?1").
Proof.
intros segs mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
- cbn in H1. injection H1 as <-. cbn [app].
rewrite word_add_0 in H2. exact H2.
- change (S n1 + n2)%nat with (S (n1 + n2))%nat.
cbn [rdn] in H1 |- *.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|]; [|discriminate].
destruct (rdn segs mem (a+1) n1) as [rest|] eqn:Er; [|discriminate].
injection H1 as <-.
rewrite (IH n2 (a+1) rest bs2 Er); [reflexivity|].
replace (a + 1 + nat_to_word n1) with (a + nat_to_word (S n1))
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
exact H2.
Qed.
Lemma rdn_nth : ltac2:(TCodec.tc2 tcn__SeqExec "QF'7'O%211'TMyR0%211':y8%511%311p051'8%<14'@%812&REr6r5r3r4%544321(1r2%22;1%;3:41&E%1249r8r7&TN&N%11=%33L?1u1%C47621(4&G&TLz%22Q01%44Q0FE1(9%11Q2%83Q331%G2Q01%Q03O;1p0D1p0G1pXBQ51pWJQ51pWDQ=1pXLQ81pXJQ:1pYBQC1").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs j H Hj; [lia|].
cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct j as [|j].
- rewrite word_add_0. cbn [rdn nth]. rewrite Eb. reflexivity.
- cbn [nth].
replace (a + nat_to_word (S j)) with (a + 1 + nat_to_word j)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest j Er). lia.
Qed.
Lemma v_addi_m : ltac2:(TCodec.tc2 tcn__SeqExec "N'TMyR0%211'J&S=r1&U2r2%2271%5241&S?z%2215'@&RHr4&SEr3%211%5241&TL&SH%@2E7%2216%42G1%<3G61p0>1p0B1pXDI1pZBK1").
Proof. intros x k _ _. reflexivity. Qed.
Lemma rdn_skipn : ltac2:(TCodec.tc2 tcn__SeqExec "Q@'7'O%211'TMyR0%211':y8%511%311p051'8%<14'@%812&REr6r5r3r4%544321(1r2%22;1%;3:41'D%1249r8r7&TN&N%11=%33L?1&C%12B@%D48731&H%13MCB%A2J1%J3I41p0>1p0A1pXDO1pWJO1pWDQ71pXLQ21pXJQ41pYBQ=1").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
- assert (k = 0)%nat by lia. subst k. rewrite word_add_0.
cbn in H |- *. injection H as <-. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct k as [|k].
+ rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
+ cbn [Nat.sub skipn].
replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply (IH (a+1) rest k Er). lia.
Qed.
Lemma rdn_firstn : ltac2:(TCodec.tc2 tcn__SeqExec "Q:'7'O%211'TMyR0%211':y8%511%311p051'8%<14'@%812&REr6r5r3r4%544321(1r2%22;1%;3:41'D%1249r8r7%>421<;&F%13G=<%;2D1%D3C41p081p0;1pXDI1pWJI1pWDQ11pXLL1pXJN1pYBQ71").
Proof.
intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
- assert (k = 0)%nat by lia. subst k. cbn in H |- *.
injection H as <-. reflexivity.
- cbn [rdn] in H.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
as [b|] eqn:Eb; [|discriminate].
destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
injection H as <-.
destruct k as [|k]; [reflexivity|].
cbn [rdn firstn]. rewrite Eb.
rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.
End WithFP4.
