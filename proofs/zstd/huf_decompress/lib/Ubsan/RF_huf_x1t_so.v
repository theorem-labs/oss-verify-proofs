(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufTableX1 HufPure_HufTableX1RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model
  RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_top RF_huf_x2t_fr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x1t_so () := "C5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List9nth_errorC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C47Corelib4Init5Peano2ltI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C47Corelib4Init5Logic3notC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas@nth_upd_nat_sameC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmasAnth_upd_nat_otherC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z3maxK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so5agreeC45stdpp9bitvector;definitions7Z_to_bvc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_soBnth_error_upd_samec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_soCnth_error_upd_otherc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so9Znth_ZupdC56Stdlib6ZArith6BinInt1Z3powC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx32K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_tbl_kitAzx32_unsigned_litI47Corelib7Numbers7BinNums1N00C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions9bv_signedC45stdpp9bitvector;definitions>Z_to_bv_signedI47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so6so_invK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model6omergeC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model=omerge_lengthC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX19sort_loopC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model;sort_loop_SC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6ostoreC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model8store_OkC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model9ostore_OkC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC46Stdlib9micromega;ZifyClasses6eq_iffC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z6shiftlK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u32arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le4K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u32arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:upd_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_frameC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp8oupd_natC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model<omerge_storec5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so9agree_updC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas>upd_nat_lengthC5ARocqVerifyHarness?AgentSubmission4SpecCHufPure_FseDecompRT?oupd_nat_lengthK47Corelib4Init5Logic3and01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so:zx32_smallC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC46Stdlib9micromega;ZifyClasses9and_morphC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init5Logic4True00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so=sort_step_invK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltsc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so?signed_small64'c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_so3so1C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC47Corelib4Init2WfFwell_founded_inductionC46Stdlib5Arith6Wf_nat5lt_wfK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition agree (tl : Z) (rs : list Z) (rsw : list word) : Prop :=
  forall i, 0 <= i <= tl -> nth_error rsw (Z.to_nat i) = Some (Z_to_bv 64 (Znth i rs)).

Lemma nth_error_upd_same : forall {X} (l : list X) i x, (i < length l)%nat -> nth_error (upd l i x) i = Some x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_so ()) [] "p'0h01Hh11ih21xh34__x1h41lh52H0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4cstrh=2IHh>1Xh?5cstr0h@1yi001np;1p;2p;4p;3p;6p;5p;<p;7p;8p200R0g0000R1p4p710p8P0g000`R2p4p710p8P0g001BR3p4p710p8P0g001bR4p4p710p8p1002@p4p7210p1002lp4p710p8g003Jj1>TP3j20Tg003jR3j21Tg004Bj18TP1j4:TP4j39Tg004dj25Tg005Fj37Tg005`j1@Tg006@R4j12Tg006`R1j26Tg007<j23Tg007Vj4LTg008=j1CTg008bj2=Tg009>j2JTg009\j1XTg00::j1WTg00:ej2ITg00;Hj2HTg00;kj4GTg00<Vj1VTg00=8j6UTg00=\j2TTg00>>j2QTg00>jj3PTg00?Ij4OTg00@;j3?Tg00@[R5j14Tg00A:j1NTg00AXj2;Tg00B5j1RTg00BSj4STg00C1j3FTg00CTj1^Tg00D9j4]TP2j5\Tg00Ddl<KTg00EIj7[Tg00Emj8ZTg00FQl<YTg00G6R2g00GUR6P3P4P1g00H3R7f3R8f2R9f1R:g00HUR;g00I4R<f0R=M<Kp=MP:g00IRR>g00J1R?P?g00JQR@P=g00K1F[p=<P6P:g00KQP=CGp=AP8P>P?P?P@P9P:P=GZp=BP2P6P3P4P1P7f5R7f4R1P8P9P:P=M<Kp=EP2P2P6P6P5P4P4P8g00L8P9P:P=M<Yp=D%>=P:%>:1019,1:%87P7P8P9P:C:=979157:37[^28^12W4%@8,08,1:119;%29R4/6<R5P9P41364136<CMP=CLP5%C8%28,=<p-0R5g00L\R3#@RA%>3R31J6:%X6RB%W6RCP61I6<RDg00MHg00MoRE,H6RFCG,<C%V?RGPC1AFD,<CPGPCP>P?P?P@P8EUCBCB1TC@R@P=P9g00NTR?g00O4R>'31Q=9=7?>dAP6<:COR>b7b9b:X36W81=<=16:<P8[[^36^85P=f7R5#8P5%@5P7P1C:=957155137%27R?P:P9O4b6b<b5W0X29X12%>91079,1:f6RD#8PDP8P9P:C:=9D915D:37[^21^12A?D18,0D,1:P2f8RH/07#4,1=f9RI#8PIA?I5DP:P8C:=9I:15I837]0P91051#4,1;%8H15H9'3W0%4=10ID#4'1PDP:P1f:RD/05R;,1:%2:RJ%2;RK'6P:PJ136JRLP;PK136KRMEE%4:RN%4;RO'1%NERP,;J1;KP'6RQPN1;=PRRX26RSPJO1PSP:PJPLCDPOPSPKO1PSP;PKPMCDEEP=CLPQ%C91=<4f</0IRI#C%2I,=<PAP3P61J69P:%R6CSPBPC1I6PRB9F6F%^E,H6RE=F6B'A,<CPG1AFE,<CCBP@P>b7b9b:X36X;61;:P,6R16:9[^36^;6P=f>f;'0#2P?P8O3b6b?b<b5C]O3%8DPDA?DH5PNP1C:=9DN15D137eW0X12P=O1n0110000020011100P=O1W0X27X12W=W4X@:P=D\W4X>0o"). Qed.

Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j -> nth_error (upd l i x) j = nth_error l j.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_so ()) [] "p'0h01Hh11jh21xh31ih41lh52H0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x1h<4__x2h=1yh>2IHh?1Xh@4cstrhA5cstr0i001np;1p;3p;2p;4p;6p;5p;<p;7p;8p200R0p1002lp4p710p8P0g0000R1p4p710p8P0g000`R2p4p710p8P0g001bR3p4p710p8g003Jj1;Tg00OTj10Tg004Bj14TP3j31Tg005`j1MTg007<j26Tg00@;j39Tg005Fj33j1GTg006@R3j1:Tg00Omj2kTg00PPj3dTg00Pmj3ATg007Vj4JTg00B5j1ZTg009\j1XTg00::j1WTg00:ej2HTg00<Vj1VTg00=8j6UTg00=\j2TTg00>>j2STg00>jj3RTg00?Ij4QTg004dj2DTg00@[R4j18Tg00A:j1PTg00AXj2<Tg008=j1FTg008bj2OTg00QVj2NTg00R?j1lTg00R]j2jTg00S>j3iTg00Sgj3hTg00TPj2cTg009>j2bTg00BSj4_Tg00;Hj2ITg00C1j3KTg00CTj1]Tg00D9j4\TP2j5`TP1j4aTg00Ddl<LTg00;kj4[Tg00EIj7eTg00U<j6YTg00Emj8fTg00FQl<gTg00G6R1f1R2f0R533p=5f7R6f6R7f5R8f4R9f3R:f2R;Ca;12;35p=2g00HUR<=315p=@g00GUR=?325p=7P1P=P9P3P:P;P<g00I4R>P2P<P>P5M<Lp=^P=P2g00U`P5C[p=?P2g00IRR?g00J1R@P@g00JQRAP5g00K1Fep=>P2P?P@P@PAP5EYp==P:P?P@P@PAP;P2P5Gfp=EP1P=P5P3P2P;P:P9P8P7P6f8RBM<Lp=CP1P1P=P=P4P3P3P:g00L8P;P2P5M<gp=B%;5P2%;215;2#0R3%47P7P7P9P:P2P;A179;G2[^29^11^31W4%48%M8=18;'6X03X2:X11X31%;;%46P6P6P9P:P2P;A169;G2\3^28^11^31P1155:#0f:R4#4RCP4P4A94B6RDP2P:P9A14D9G2]0P:%@;#0P1%@5#0f;RE#4PEPEf9RF=9EBRGP<P9P2A1EG2G2]0P:A31<<RG#0RHPHA3=>>RH#0RI%G1RJ%G=RK%:2RL%:5'715251k253dX=1X21RM16=>RNPND^9AGHP5CJPIp-0RIg00L\RG#MRN%;GRO%Z=RP%X=RQ%W=RR1H=>RS/?S,>R,=R%V@RSPRP?P@P@PAP;EUCE1TRARAP5P;g00NTR@g00O4R?'61S5;=3@?dAR=>2CQR?b7b9b:W8g00VGR@\HP2[^8IP5f<RI#4RH1DI81DI4RT33P2O2b6b5PCP4P4PDP<P:P<A14D<G2eW0%85RD#@#0A1IF2,6HPHPIPIA9I4FRFP<P8%82RCA1IFCG2eW0X11P5O1n0110000020010100P5O1W015D9#0P1%8;RU/55#0f=RV#4PVPVA9VE4RW%8:RXP7P2A1VW2G2]0P8A31C<#016HTPHPIPIPFPUP8P<A1IF<G2eW015XD#0P4P9P2P61592R4#0%:9RX/7LRD#0PJPKPMP9PX16=XRFP2PL16=LRUM9C9A4D%89RD/5CR4#0g00MoRH#PRT,<X1<LT'7#0RW1<5TRVX2=RYPXO1RZPYPLO1R['7PJPKPMPDPZPYP9PXPFCBPCP[PYP2PLPUCBM9C5A4P5CJPW%F8%:8R8,O>%F:%::,O>%8<,N=%lH,j=1N=<5i=5h=g00Vd'c=9GNPOP=1b=;P2PPC_PQPR1I=HRQ1H=TRP5K=%]H,I=RH=K=P'?,>R,=RPS1?QH,>R,=RCEPAP?b7b9b:X;=X<=1<2T,7VP@[172;P@[[^;=^<=P5P8%:BP:O3b6bAb@b5C\O4f>R:#4P:P:A9:IERIPDP6PCA1:ICG2eW0X11P5O1n0110000020011100P5O1W0X31P5O1n0110000020111100P5O1X03X27X11X31W>W4X=2P5D`W4X?0o"). Qed.

Lemma Znth_Zupd : forall (l : list Z) i j v, 0 <= i -> 0 <= j -> (Z.to_nat i < length l)%nat ->
  Znth j (Zupd i v l) = if i =? j then v else Znth j l.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_so ()) [] "p'0h02Hjh11xh24__x1h34__x2h44__x3h54__x4h61jh72H0h82H1h92Hih:2Hlh;3Hl0h<1Nh=7__arithh>4__ffh?8__varmaph@5__withA1bi001bhB4cstrhC1ei011ehD1ihE1lhF1ri021rhG1vhH1yhI2z0hJ2z1i031np&0p;1p;2p;3p;4p;7p;<p;5p;6p;8g003Jj1XTg008bj22Tg00WPR0j1;Tg001Bj2HTg003jR1j2[Tg00X0j2rTg00XRj2ZTg00XoR2j2cTg00YRj3PTg00ZMj4_Tg00[Qj7]Tg00OTj1LTg005Fj3=j1WTg006@R3j1DTg00Omj2pTg00PPj3jTg007<j2BTg00Ddl<RTg00Pmj3eTg006`R4j2>Tg007Vj4aTg008=j1`Tg00[mj2OTg00\Oj24Tg00\jj2?Tg00@[j17Tg00R?j1^Tg00R]j2\Tg00S>j3KTg00QVj2NTg005`k100Tg009>j2YTg00B5j1~Tg00BSj4MTg009\j1}Tg00::j1|Tg00:ej2{Tg00]Dj1qTg00;Hj2FTg00;kj4ATg00<Vj1oTg00CTj1TTg00=\j2iTg00>>j2kTg00>jj3lTg00?Ij4hTg00D9j4mTg00]ij5nTg00^nj3gTg00_fj2VTg00`^j4fTg00a:j2sTg00FQl<tTg00Sgj3JTg00TPj2dTg00@;j3uTg00EIj7vTg00aWj7wTg00b;j7xTg00U<j6yTg00Emj8zTg00GUR5f1R6f0R73=p=0P5P6P7g00I4R8Cfp=I1s87p=6P5g00G6R9P5P5P0f4R0P3f3R:g00b_f2R;P6P7M<tp=QP9P5P1P3P4g00H3f5R4P0P:P;P6P7M<Rp=bA=578p=@1N57p=5AJ5679J5;p=9g00Vd,d7p=:AJ567p=Gg00L\R1?u67p=3P6g00IRR<g00J1R=P=g00JQR>P7g00K1Fvp=1P5P6g00U`P7CAp=8P;P<P=P=P>P6P7Fwp=CP5P6g00MHP7CAp=EP;P<P=P=P>P6P7Fxp=UP6P<P=P=P>P7Eyp=SP:P<P=P=P>P;P6P7Gzp=<%X5128;R<%;01H54'[1r4010401Z40R?'cf6R@/Z4g00NTRAP2f7R2/0@f8RB#;RCf9RD#;REf:RF7P2'IPAP5P6P21ICFn0100000020000'0P610B2RGP5PD1287%;6f;RH#;f<RI7PD'I/0D]0X65128D%;FPBPHP4C_W0PBP7P4F]WCP7O1%LGPEPCP2PFA=9ECRG#L%6DRJ%6BRK'0RL#LP9P5%W9P3%W5%D6%D7'0A=9671p673jXH9X19PEPJP7X15R9%67X15R3PDPD1B5DDQRMPCPKP9P3PBPB1B5BDQM<R9eGL1H5FRL,[E%DLRG,>JRJPEP3PDO1PMPLPG1B5GEbP0CaPJ1H5HRJ#`%DJ,281O8F1>8F%6FRJ/0F'412F8%@J'4'?%6HP5f=RH,O81>8H%6HRJ/0H'412H8%@J'4'?f>#6P5g00HURJ#7RF#7RG#7RL#7RM#7RD#7R3#7#5RE%5LRL%5G39#:RG%5DRD%5F79L#:RF%53R3g00MoRB#^,\5R9%5MRM5K5RK1N5JRJ9K59RC'G79D#:AK593R91GLJ79M#:1GLC993K#:1GMJ99E9#:&001'3,3F'3'3,3G'3'3'3%X1P5P51Y50P;%~5CMP61Y5:CM%}5%|5R1P51{58RGg00KQRF%qB,F5R9CA,111F5BRE/89,115C11E9G,1118EG,115C15U1%o=R=P1P5PGPF%TBRB#T,F5RFCA,111F5BRB/8F,115C11EFG,1118BG,115C15U1P=P1189F,11,S1P=P11EGF,11P=P11EG9,11P=18EB,11,S1C<C<C<C<C<1i1>P7P;g00O4R1,BA1k7;==A1dAl586Chb>b?b@X25X35X45X551>8;107;'412;8%@7'4'?1>8010;0'41208%@;'4'?1004g00VGR1[128@R8104@P1[\8[[[[^25^35^45^55P7f?f@P:P6P;P0P2PIPHO9b=bJb8bIb7bBb;CmDnW<P7O1n10210010200021010111103bAbFAg4:@,V0PAP5P?P:1V0@n0100000020000'0eW:X0<W9XG5X65XD5WEo"). Qed.

Lemma agree_upd : forall tl rs rsw w v, agree tl rs rsw -> 0 <= w <= tl -> (Z.to_nat w < length rsw)%nat ->
  (Z.to_nat w < length rs)%nat ->
  agree tl (Zupd w v rs) (upd rsw (Z.to_nat w) (Z_to_bv 64 v)).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_so ()) [] "p'0h03Hl0h14__x1h22H3h37__arithh44__p1h54__x2h64cstrh75cstr0h82z3h92Hih:4__ffh;8__varmaph<5__with=1xh>4__p2h?4__x3h@4__x4hA1ihB1AhC2H4hD3Hl1hE3Hl2hF2HwhG1NhH1bi001bhI1ei011ehJ1ohK1ri021rhL2rshM3rswhN2tlhO1vhP1whQ1yhR1zhS2z4i031np&0p;1p;3p;2p;4p;5p;7p;<p;6p;8g003Jj1\Tg00CTj1FTg00cLj1yTg00cjj1kTg00dMj3iTg008bj22Tg00\Oj20Tg00WPR0j17Tg001Bj26Tg003jR1j2BTg00XRj2^Tg00_fj2OTg004Bk10<Tg00eKj2=Tg0000j4STg001bj3PTg004dj2RTg005Fj39j1fTg00X0j2|Tg00XoR2j2{Tg00f1j5xTg00[Qj7wTg00OTj1UTg006@R3j18Tg00Omj2oTg00PPj3mTg00Ddl<_Tg00Pmj3jTg006`R4j24Tg007Vj4MTg008=j1LTg00[mj2TTg00\jj2KTg00@[j1@Tg00R?k10;Tg00R]k20:Tg00S>j3]Tg00QVj2hTg005`k109Tg009>j2[Tg00B5k108Tg00BSj4ZTg009\k103Tg00::k102Tg00:ek201Tg00]Dj1eTg00;Hj2NTg00<Vj1zTg00=\j2vTg007<j2bTg00>>j2tTg00>jj3sTg00?Ij4uTg00D9j4gTg00g<j6rTg002lj6aTg00^nj3`Tg00hHj7qTg00a:j2}Tg00FQl<~Tg00Sgj3WTg00TPj2pTg00@;k300Tg00;kj4YTg00EIj7nTg00aWk704Tg00b;k705Tg00U<k606Tg00=8k607Tg00Emj8lTg00I4R5f0R6'2p=:g00GUR7f1R8;96p=31}56p=51b76p=;P7g00G6R9P7P7P0f4R0P3f3R:g00b_f2R;P8P6M<~p=GP9P7P1P3P4g00H3f5R4P0P:P;P8P6M<_p=JA9765p=I1h76p=AAW7869W7;p=Eg00Vd,p6p=DAW786p=Qg00L\R1@0086p=<P7P8g00KQP6CYp=XP8g00IRR<g00J1R=P=g00JQR>P6g00K1Fnp=1P7P8g00U`P6CYp=CP;P<P=P=P>P8P6K04p=>P7P8g00MHP6CYp=HP;P<P=P=P>P8P6K05p=dP8P<P=P=P>P6J06p=cP8P<P=P=P>P6J07p=VP:P<P=P=P>P;P8P6Glp=?%\7g00MoR<#FR?#F#F#F#F#F#yR@#kRA#\Ai0:;%:;12;4'0%7:16A0'B%70f6RB,67'B%:6RCf9RD,26'0P7g00NTREP7f7RF/^8RGPB1O8Dn0100000020000&0<ARHPAPDf8RI#7RJ1=@FCS%7;5PA1=@6,RA39XR71|F813F8/{G1^I;PEP213D:PAf<R2f;RG#7RKf:RL,=@RMCS%74RN5PAROPEP7P8PLf=RP,O4n0100000020000,=@,RA59HP813L0RQP7PGf?,26,0CPAf>RR%7P1=@2RSCS%785PA1RAS59H]9XA7%:G12GR'0PAPP%72RS1=@GPIDxW9P4P6P0FwWIP6O1%UQPHAPA2N1OBR,=@,RA99H6XJHPDP4P0O2POPAP2PKPNPMA99KNRM#U%5GRO%54RH'3RQ#UP9P7%f9P3%f7%88%86'3A99861o863mXQ9X=9PKPOP6X=7R9%56X=7R3PGPG%;GDGRTPNPHP9P3P4P4%;4DGM<_9jMQ167PRQ,BK%8QRM,4ORHPKP3PGO1PTPQPM%;MEJPBCMPH16APRH,BS%52RM%8HRQ'4RTPSP3P2O1P9P3P2P2%;2DGPHPQ%;QEJPICMPT16ARRT#L%8T#:f@,67RT#L%8TRT#:1T5D145D%5DRQ/3D'012D5%IQ'0'K%5LP7fARQ,T5145Q%5QRH/3Q'012Q5%IH'0'KfB#5P7p-0RHg00HURS#@RK#@RU#@RV#@RW#@RX#@RY#@#ARZ%AVRV%AU3E#DRU%AXRX%AK7EV#DRK%AYRY&0;<-0:7R[%AWRW5]7R\1h7SRS9]7[R]'Q7EX#DA]7[YR[1QVS7EW#D1QV]9EY\#D1QWS9EZ[#D&091R['<,<K'<'<,<U'<'<'<%\1R1P71[7;RUP8P71[70P:&087RKCZCZ&037RZ&027RS20175RW%e<,N7R\'X,1S1N7<R</C\,1S5>S1H\W,1S1C<W,1S5>S5dS%z=R=PS%e?,N7RY,XW,1S1N7?R?/CY,1S5>S1HYW,1S1C?W,1S5>S5dSP=PS1C\Y,1S,cSP=PS1HWY,1S1VSB5>SP=PS1HW\,1S1VSF5>SP=1C<?,1S,cSC?C?C?C?C?1vS>R>P6P;g00O4R\,bE1t6;=9E\dAs758CuR\b:b;b<X17X57X?7X@7X4HW>145;136;'012;5%I6'0'K145013;0'01205%I;'0'K1304g00VGRE[%:BRY/0F10YD134BPE[[[[[[^17^57^?7^@7^4H^>HP6fDREfGRY'212RYPRPEP:P8P;P0PDPPPQO;b3bSbCb8b2b7b6b0b0CgErEaWGP6O1n10210010200021010111103bHbKA`FBD,O8PDPFP8PB%7FRP167DRE'BRY%5FR]%8ERV'4RXPPP3PFO1P9P3PFPF%;FDGR^PEPV%;VR_EJP;CMR`PX16ADRD,BJ%5I%8DRa'4RbPJP3PIO1P9P3PIPI%;IDGPDPa%;aEJP0CMRaPb16ALRL#LRD%8L#:RL1672R2#LR3%82#:R21T5GR9145G13OG'012G5%IO'0'KROPMP7P[P11[78PZPS1HW<,1SRW1VS:5>SP=PWC?P>P\b:b;b<X17X4HRW10C8%:8[^17^4HRHP612RQPRPGO3b3b8b2b7b6b0b0P`PXPaPbPDPLP3P2P9POPMP7PWPHP612IQPIPFO3b3b8b2b7b6b0b0PYPXPPP]P^PEPVP_EJP`PXPaPbPDPLP3P2P9POPMP7P[P1P7PUP8PKCZPZPS1X<?,1SRSP=PSC?P>P\b:b;b<X17X571468148;[^17^57P6PTP8PBO3b3b8b2b7b6b0b0CgFqEaW9XA7A`40FPAPBPN1=@0CS5iIeWEWDWFWBXO7XP7WMWLXN7o"). Qed.

(* [comment removed for export] *)
Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_so ()) [] "h01zh14__x1h22b1h32b2h41nh51Hh62Hzh77__arithh84__ffh98__varmaph:5__witp;2p;1p;3p;4p;8p;6p;7g008bj2ATg00CTj12Tg00A:j16Tg00iJj2>Tg006`j2?Tg00\OR0j2;Tg00cjj13Tg005Fj30Tg00igj21Tg00jQj3FTg00cLj17Tg00eKj2=Tg00k5j1BTg007<j2@Tg005`j1STg003Jj1RTg009>j2QTg009\j1PTg00::j1NTg00:ej2:Tg00;Hj2MTg00;kj45Tg00kfj39Tg00<Vj1HTg00Emj8GTg00=\j2ITg00>>j2JTg00>jj3KTg00?Ij4LTg00lIj2ETg002lj6<Tg00mEj2DTg00EIj7CTg00aWj7OTf1R1g00IRR2g00J1R3P3g00JQR4f0R5g00K1FCp=4f2R6P2P3P3P4P1P5FOp=8g00GUR7g00I4R8/A5g00MoR9#2R:#6R;%2:#2#2#2R:#6'>,?5';R<g00nPR=%35R>%31R?P0%36?015f3R0/161101507R@[11611165507%30?061[RAf4#3?006\@AF615P5n2001000000120000000W3W2W4PA^3?^2>^4=P5%2:R=#7R>1=>6R?#BRAP?P7P61=>0,1>9075X07P7P6A0705X071@7611>?g00L\R?#S%R?1Q71%P7%N7R?P2P3P3P4P71:78g00MH1M79R9C5,4?R2P7P9g00KQR@1:7;RB%7:597C5,4?58?%H3P7P9P@A97B>C5,4?98?2GG1I?4P5P6g00NTR?g00O4R4'@1J56=0?4dAK781CLb8b9b:X171A81%6=,>;,?1';\<^17P5P0P6O2b7,E6E<11>A1D61E<O4b5W6W0o"). Qed.

Lemma signed_small64' : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_so ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh61Hh71xp;2p;1p;3p;4p;8p;6p;7g008bj2<Tg00CTj10Tg00A:j16Tg00]Dj14Tg00iJj2XTg006`j28Tg00\Oj27Tg00cLj1DTg00nnj2CTg005Fj33Tg00AXj2=Tg00oUj2>Tg005`j1VTg003Jj1UTg009>j2RTg009\j1QTg00::j1OTg00;Hj2NTg00:ej29Tg00C1j3MTg0102j3ETg00;kj42Tg00=\j2GTg007<j2HTg00>>j2ITg00>jj3JTg00?Ij4KTg010Uj2LTg00<Vj1BTg00Emj8ATg0115j3@Tg002lj6;Tg00eKj2PTg011Xj2?Tg012@j2STg00EIj7TTg00aWj7WTf0R0#0#0#0#0p=F%00#0#0#0#0#0#0#0p=1f1R1g00IRR2g00J1R3P3g00JQR4P0g00K1FTp=5f2R5P2P3P3P4P1P0FWp=:g00GUR6g00I4R7/<0R8g00MoR9#0R:#6%49#4#4#4#4#6'X,80'7P6%0:#FR:#DR;/C1R<A3605X56P6%0:#1#1#1#1#1#1#1R:#6R=,=1R>1>0==365X56g00L\R?#VR@%U?R?1R61RA%Q6RB%O6RCP61N69R9196=RD5M6RE=E6Dg00U`P9C2'51GC4RFP0P5g00NTRGg00O4RH'H1I05=3GHdAJ671CKRHb2b3b4X061=0=/>==360^06P0P5O1b1%0:#6R:,L>P@P?PAPBPCP2P3P3P4P61967R4g00MHR2P9C2,5CP6P9g00KQR9PDC2,5C5:C%B3P6P4P2PEC2,5CP6PEP9196:C2,5C5:CGAPFPHb2b3b4X06180=,781<7>18>:'7[^06P0P5P1O2b19@>:E;A36<1e1P;1,?;1S;1E;W6W7o"). Qed.

Lemma x1s_load : forall l i, 0 <= i < zlen l -> FseNCount.load l i = Ok (Znth i l).
Proof.
  intros l i H. unfold FseNCount.load, FseNCount.Zlength.
  rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.ltb_lt i (Z.of_nat (length l)))) by lia. reflexivity.
Qed.

Lemma x1s_store : forall l i v, 0 <= i < zlen l -> FseNCount.store l i v = Ok (Zupd i v l).
Proof.
  intros l i v H. unfold FseNCount.store, FseNCount.Zlength.
  rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.ltb_lt i (Z.of_nat (length l)))) by lia. reflexivity.
Qed.

Lemma x1s_u8lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
  change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma x1s_nth : forall (ws : list Z) (jk : list byte) k, 0 <= k < zlen ws ->
  nth_error (map (Z_to_bv 8) ws ++ jk) (Z.to_nat k) = Some (Z_to_bv 8 (Znth k ws)).
Proof.
  intros ws jk k H. rewrite nth_error_app1 by (rewrite length_map; lia).
  rewrite nth_error_map. unfold Znth. rewrite (nth_error_nth' ws 0) by lia. reflexivity.
Qed.

Lemma x1s_shl2 : forall v, Z.shiftl v 2 = 4 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma x1s_povf : forall A n, 0 <= n < 2^63 -> 0 <= A ->
  Z.lxor (Z.lxor (Z.b2z (A + n <? A)) (Z.b2z (Z.lxor n 9223372036854775808 <? 9223372036854775808))) 1 = 1.
Proof.
  intros A n Hn HA.
  rewrite (proj2 (Z.ltb_ge (A + n) A)) by lia.
  replace (Z.lxor n 9223372036854775808) with (n + 2^63) by (symmetry; apply (zb_lxor_pow2_small n 63); lia).
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Local Ltac x1s_modsmall := match goal with |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia end.
Local Ltac snorm := repeat (first [ rewrite x1s_u8lit by lia | rewrite x1s_shl2 | rewrite x1s_povf by lia | x1s_modsmall ]); x1w_norm.
Local Ltac swalk := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => snorm; first [ x1w_dec_if | x1w_ck | x1w_decl ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => x1w_inr; snorm; zstep
  end).
Local Ltac swto o := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => snorm; first [ x1w_dec_if | x1w_ck | x1w_decl ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in (z =? PHUF_RDT_X1 + o) in lazymatch d with true => fail | false => snorm; zstep end
  end).

Local Ltac xst A ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ A _ q (wa (A + q)) ARR ltac:(first [ lia | rewrite ?upd_length, ?omerge_length; lia ]) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (A + q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (A + q) by lia
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?x)) _) =>
    first [ match goal with H : le1 x = [_] |- _ => rewrite H end | rewrite le1_lit ]
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write usegs _ A _ q bb ARR ltac:(first [ lia | rewrite ?upd_length, ?omerge_length; lia ])) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.

Local Ltac xst4 A ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok usegs _ A _ q (wa (A + 4 * q)) ARR ltac:(first [ lia | rewrite ?upd_length, ?length_map; lia ]) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (A + 4 * q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (A + 4 * q) by lia
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?bb)) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u32arr_write usegs _ A _ q bb ARR ltac:(first [ lia | rewrite ?upd_length, ?length_map; lia ])) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.

Section SO.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m : fmem) (FB W nbS tl r DT : Z) (ws : list Z) (L js : list byte).
  Variables (c1 c2 : word) (j8 j16a j16b j16c j24 : list byte).
  Variable POST : machine_state -> Prop.
  Notation RS := (W + 52).
  Notation SY := (W + 980).
  Notation HW := (W + 1236).
  Notation FRAME := [C8 c1; C8 c2; CB 8 j8; C8 (Z_to_bv 64 r); CB 16 j16a; C8 (Z_to_bv 64 DT);
                     CB 16 j16b; C8 (Z_to_bv 64 (tl + 1)); CB 16 j16c; C8 (Z_to_bv 64 W); CB 24 j24].
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HNS : 2 <= nbS <= 256.
  Hypothesis LWS : zlen ws = nbS.
  Hypothesis WSR : Forall (fun w => 0 <= w <= tl) ws.
  Hypothesis LL : length L = 256%nat.
  Hypothesis NBL : forall k, 0 <= k < nbS -> nth_error L (Z.to_nat k) = Some (Z_to_bv 8 (Znth k ws)).
  Hypothesis HJS : length js = 256%nat.
  Hypothesis HWB : 0 < W /\ W + 8704 <= FB.
  Hypothesis HFB : FB + 240 <= 2^47.

  Definition so_inv (m1 : fmem) (rs : list Z) (syms : list (option Z)) (rsw : list word) : Prop :=
    u32arr usegs m1 RS rsw /\ length rsw = 13%nat /\ agree tl rs rsw /\ zlen rs = 13
    /\ u8arr usegs m1 SY (omerge js syms) /\ length syms = 256%nat
    /\ u8arr usegs m1 HW L /\ rw_cells usegs m1 FB FRAME
    /\ munch [(RS, RS + 52); (SY, SY + 256)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Lemma so_pre : forall k n rs syms rsw m1 r0, sort_loop k n ws rs syms = Ok r0 -> Z.of_nat k = nbS - n -> 0 <= n < nbS ->
    so_inv m1 rs syms rsw ->
    exists k' w p, k = S k' /\ 0 <= w <= tl /\ 0 <= p < 256 /\
      nth_error L (Z.to_nat n) = Some (Z_to_bv 8 w) /\ nth_error rsw (Z.to_nat w) = Some (Z_to_bv 64 p) /\
      sort_loop k' (n + 1) ws (Zupd w (p + 1) rs) (oupd_nat (Z.to_nat p) n syms) = Ok r0.
  Proof.
    intros k n rs syms rsw m1 r0 SL FK NR INV.
    destruct INV as (RSA & LRW & AG & LRS & SYA & LSY & HWA & FRA & MU & WM & MI).
    destruct k as [|k']; [lia|].
    assert (WR : 0 <= Znth n ws <= tl)
      by (unfold Znth; exact (proj1 (Forall_nth (fun w => 0 <= w <= tl) ws) WSR (Z.to_nat n) 0 ltac:(lia))).
    rewrite sort_loop_S in SL.
    rewrite (x1s_load ws n) in SL by lia. cbn [bind] in SL.
    rewrite (x1s_load rs (Znth n ws)) in SL by lia. cbn [bind] in SL.
    rewrite (x1s_store rs (Znth n ws)) in SL by lia. cbn [bind] in SL.
    unfold ostore, FseNCount.Zlength in SL.
    destruct ((0 <=? Znth (Znth n ws) rs) && (Znth (Znth n ws) rs <? Z.of_nat (length syms)))%bool eqn:E; [|discriminate].
    apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    cbn [bind] in SL.
    exists k', (Znth n ws), (Znth (Znth n ws) rs).
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [apply NBL; lia|]. split; [apply AG; lia|].
    change (u32 (Znth (Znth n ws) rs + 1)) with ((Znth (Znth n ws) rs + 1) mod 2^32) in SL.
    rewrite Z.mod_small in SL by lia. exact SL.
  Qed.

  Lemma so_inv_step : forall m2 n rs syms rsw w p vp vn, 0 <= w <= tl -> 0 <= p < 256 ->
    length rsw = 13%nat -> agree tl rs rsw -> zlen rs = 13 -> length syms = 256%nat ->
    u32arr usegs m2 RS (upd rsw (Z.to_nat w) (Z_to_bv 64 vp)) -> vp = p + 1 ->
    u8arr usegs m2 SY (upd (omerge js syms) (Z.to_nat p) (Z_to_bv 8 vn)) -> vn = n ->
    u8arr usegs m2 HW L -> rw_cells usegs m2 FB FRAME ->
    munch [(RS, RS + 52); (SY, SY + 256)] m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
    so_inv m2 (Zupd w (p + 1) rs) (oupd_nat (Z.to_nat p) n syms) (upd rsw (Z.to_nat w) (Z_to_bv 64 (p + 1))).
  Proof.
    intros m2 n rs syms rsw w p vp vn WB PB LRW AG LRS LSY RSA EP SYA EN HWA FRA MU WM MI. subst vp vn.
    rewrite omerge_store in SYA by lia.
    unfold so_inv.
    split; [exact RSA|]. split; [rewrite upd_length; exact LRW|].
    split; [apply agree_upd; [exact AG | lia | lia | lia]|].
    split; [rewrite Zupd_length; lia|]. split; [exact SYA|]. split; [rewrite oupd_nat_length; exact LSY|].
    exact (conj HWA (conj FRA (conj MU (conj WM MI)))).
  Qed.

  Local Ltac sstep :=
    lazymatch goal with SL : sort_loop ?k ?n ws ?rs ?syms = Ok ?r0, INV : so_inv ?m1 ?rs ?syms ?rsw |- _ =>
      let k1 := fresh "k" in let w := fresh "w" in let p := fresh "p" in
      let WB := fresh "WB" in let PB := fresh "PB" in let NB := fresh "NB" in let NV := fresh "NV" in
      let SL1 := fresh "SL" in
      destruct (so_pre k n rs syms rsw m1 r0 SL ltac:(lia) ltac:(lia) INV) as (k1 & w & p & -> & WB & PB & NB & NV & SL1);
      clear SL;
      let RSA := fresh "RSA" in let LRW := fresh "LRW" in let AG := fresh "AG" in let LRS := fresh "LRS" in
      let SYA := fresh "SYA" in let LSY := fresh "LSY" in let HWA := fresh "HWA" in let FRA := fresh "FRA" in
      let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in
      destruct INV as (RSA & LRW & AG & LRS & SYA & LSY & HWA & FRA & MU & WM & MI);
      let RD1 := fresh "RD" in
      pose proof (u8arr_read usegs m1 (W + 1236) L n _ (wa (W + 1236 + n)) HWA NB ltac:(lia) eq_refl) as RD1;
      swalk;
      let RD2 := fresh "RD" in
      pose proof (u32arr_read usegs _ (W + 52) rsw w _ (wa (W + 52 + 4 * w)) RSA NV ltac:(lia) eq_refl) as RD2;
      swalk;
      xst4 (W + 52) RSA w; swalk; xst (W + 980) SYA p;
      pose proof (so_inv_step _ n rs syms rsw w p _ _ WB PB LRW AG LRS LSY RSA ltac:(lia) SYA ltac:(lia) HWA FRA MU WM MI) as INV;
      clear RSA SYA HWA FRA MU WM MI LRW AG LRS LSY NB NV; try clear RD1; try clear RD2
    end.

  Notation ST4 pc mm x8 x12 n x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 FB) gp tp (Z_to_bv 64 (18446744073709551615 - (W + 52))) (Z_to_bv 64 13) (Z_to_bv 64 255) x8
             (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 (18446744073709551615 - (W + 980))) (Z_to_bv 64 (18446744073709551615 - (W + 1236)))
             x12 (Z_to_bv 64 (W + 980)) (Z_to_bv 64 nbS) (Z_to_bv 64 tl) (Z_to_bv 64 (W + 52)) (Z_to_bv 64 (nbS + -4))
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 n) x29 x30 x31)
        F (Z_to_bv 64 (PHUF_RDT_X1 + pc)) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma so4u : forall k n rs syms rsw m1 r0 (x8 x12 x29 x30 x31 : word),
    sort_loop k n ws rs syms = Ok r0 -> Z.of_nat k = nbS - n -> 0 <= n -> n + 4 <= nbS -> so_inv m1 rs syms rsw ->
    (forall m2 n2 rs2 syms2 rsw2 (y8 y29 y30 y31 : word), nbS - 4 < n2 <= nbS ->
       sort_loop (Z.to_nat (nbS - n2)) n2 ws rs2 syms2 = Ok r0 -> so_inv m2 rs2 syms2 rsw2 ->
       evt usegs POST (ST4 1292 m2 y8 (Z_to_bv 64 n2) n2 y29 y30 y31)) ->
    evt usegs POST (ST4 1036 m1 x8 x12 n x29 x30 x31).
  Proof.
    intros k. induction k as [k IH] using (well_founded_induction lt_wf).
    intros n rs syms rsw m1 r0 x8 x12 x29 x30 x31 SL FK N0 N4 INV K.
    pose proof HWB as [W0 WF].
    do 4 sstep.
    swalk. x1w_br BU.
    - match goal with SL : sort_loop ?kk _ _ _ _ = _ |- _ =>
        replace (n + 1 + 1 + 1 + 1) with (n + 4) in SL by lia;
        eapply (IH kk ltac:(lia)); [exact SL | lia | lia | lia | eassumption | exact K] end.
    - match goal with SL : sort_loop ?kk _ _ _ _ = _ |- _ =>
        replace (n + 1 + 1 + 1 + 1) with (n + 4) in SL by lia;
        replace kk with (Z.to_nat (nbS - (n + 4))) in SL by lia;
        eapply K; [lia | exact SL | eassumption] end.
  Qed.

  Notation ST1 pc mm x6 x7 x8 n x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 FB) gp tp (Z_to_bv 64 (18446744073709551615 - (W + 52))) x6 x7 x8
             (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 (18446744073709551615 - (W + 980))) (Z_to_bv 64 13)
             (Z_to_bv 64 n) (Z_to_bv 64 (W + 980)) (Z_to_bv 64 nbS) (Z_to_bv 64 tl) (Z_to_bv 64 (W + 52)) (Z_to_bv 64 255)
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 (PHUF_RDT_X1 + pc)) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Lemma so1u : forall k n rs syms rsw m1 r0 (x6 x7 x8 x28 x29 x30 x31 : word),
    sort_loop k n ws rs syms = Ok r0 -> Z.of_nat k = nbS - n -> 0 <= n < nbS -> so_inv m1 rs syms rsw ->
    (forall m2 rs2 syms2 rsw2 (y6 y7 y28 : word), r0 = (rs2, syms2) -> so_inv m2 rs2 syms2 rsw2 ->
       evt usegs POST (ST1 1412 m2 y6 y7 x8 nbS y28 x29 x30 x31)) ->
    evt usegs POST (ST1 1328 m1 x6 x7 x8 n x28 x29 x30 x31).
  Proof.
    intros k. induction k as [k IH] using (well_founded_induction lt_wf).
    intros n rs syms rsw m1 r0 x6 x7 x8 x28 x29 x30 x31 SL FK NR INV K.
    pose proof HWB as [W0 WF].
    sstep.
    swalk. x1w_br BU.
    - match goal with SL : sort_loop ?kk _ _ _ _ = _ |- _ =>
        eapply (IH kk ltac:(lia)); [exact SL | lia | lia | eassumption | exact K] end.
    - match goal with SL : sort_loop ?kk _ _ _ _ = _ |- _ =>
        destruct kk; [|lia]; cbn [sort_loop] in SL; injection SL as SLe end.
      replace (Z_to_bv 64 (n + 1)) with (Z_to_bv 64 nbS) by (f_equal; lia).
      eapply K; [symmetry; exact SLe | eassumption].
  Qed.


End SO.

Lemma x1s_rsl_len : forall f n next rank rs0 rs, rank_start_loop f n next rank rs0 = Ok rs -> length rs = length rs0.
Proof.
  induction f as [|f IH]; intros n next rank rs0 rs H.
  - cbn [rank_start_loop] in H. injection H as <-. reflexivity.
  - rewrite rank_start_S in H. unfold FseNCount.load in H.
    destruct ((0 <=? n) && (n <? FseNCount.Zlength rank))%bool; [|discriminate]. cbn [bind] in H.
    unfold FseNCount.store in H.
    destruct ((0 <=? n) && (n <? FseNCount.Zlength rs0))%bool; [|discriminate]. cbn [bind] in H.
    rewrite (IH _ _ _ _ _ H). apply Zupd_length.
Qed.

Lemma x1s_fr1520 : forall m5 A (c1 c2 r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : word) j8 j16,
  rw_cells usegs m5 A [C8 c1; C8 c2; CB 8 j8; C8 r; C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7; C8 a8; C8 a9;
                       CB 16 j16; C8 a10] ->
  rw_cells usegs m5 A [C8 c1; C8 c2; CB 8 j8; C8 r] /\
  exists cw cc : word, rw_cells usegs m5 (A + 32) [C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7; C8 a8; C8 a9;
                                                C8 cw; C8 cc; C8 a10].
Proof.
  intros m5 A c1 c2 r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 j8 j16 H.
  destruct (proj1 (rw_cells_app' usegs m5 A [C8 c1; C8 c2; CB 8 j8; C8 r] _) H) as [H1 H2].
  split; [exact H1|].
  destruct (proj1 (rw_cells_app' usegs m5 _ [C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7; C8 a8; C8 a9] _) H2) as [H3 H4].
  destruct (proj1 (rw_cells_app' usegs m5 _ [CB 16 j16] _) H4) as [H5 H6].
  destruct (cb_to_c8s 2 _ _ _ H5) as (ws & LW & H7).
  destruct ws as [|cw [|cc [|? ?]]]; cbn in LW; try discriminate.
  exists cw, cc. cbn [map] in H7.
  apply (proj2 (rw_cells_app' usegs m5 _ [C8 a1; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7; C8 a8; C8 a9] _)).
  split; [exact H3|].
  apply (proj2 (rw_cells_app' usegs m5 _ [C8 cw; C8 cc] _)).
  split; [exact H7 | exact H6].
Qed.

Section CANSEC. Context {rc : runConstT}.
Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT W S mtl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation POST := (huf_rdt_post huf_dt_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)].

  Local Ltac x1s_tail INV FIN RKr :=
    let RSA := fresh "RSA" in let LRW := fresh "LRW" in let AG := fresh "AG" in let LR2 := fresh "LR" in
    let SYA := fresh "SYA" in let LSY := fresh "LSY" in let HWA := fresh "HWA" in let FRA := fresh "FRA" in
    let MU2 := fresh "MU" in let WM2 := fresh "WM" in let MI2 := fresh "MI" in
    destruct INV as (RSA & LRW & AG & LR2 & SYA & LSY & HWA & FRA & MU2 & WM2 & MI2);
    let RK2 := fresh "RK" in let MU3 := fresh "MU" in
    pose proof RKr as RK2;
    lazymatch type of MU2 with munch ?Wl ?ma ?mb =>
      apply (u32arr_transport usegs Wl ma mb _ _) in RK2;
        [ | exact MU2 | exact WM2 | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ];
      pose proof (munch_weaken Wl [(W + 52, W + 52 + 52); (W + 980, W + 980 + 256); (bv_unsigned sp + -208, bv_unsigned sp + -112)] ma mb
                    ltac:(unfold sub_fp; cbn [outside]; intros; slia) MU2) as MU3; clear MU2
    end;
    lazymatch type of SYA with u8arr _ _ _ (omerge ?js0 ?sy0) =>
      let LO := fresh "LO" in assert (LO : length (omerge js0 sy0) = 256%nat) by (rewrite omerge_length; lia) end;
    let RD0 := fresh "RD" in
    lazymatch type of RK2 with u32arr usegs ?mm ?A (map (Z_to_bv 64) ?rk) =>
      pose proof (u32arr_read usegs mm A _ 0 _ (wa (A + 4 * 0)) RK2 (nth_error_map_Znth (Z_to_bv 64) rk 0 ltac:(lia)) ltac:(lia) eq_refl) as RD0;
      rewrite Z.mul_0_r, Z.add_0_r in RD0 end;
    swto 1448;
    let RD1 := fresh "RD" in
    lazymatch type of RK2 with u32arr usegs ?mm ?A (map (Z_to_bv 64) ?rk) =>
      pose proof (u32arr_read usegs mm A _ 0 _ (wa (A + 4 * 0)) RK2 (nth_error_map_Znth (Z_to_bv 64) rk 0 ltac:(lia)) ltac:(lia) eq_refl) as RD1;
      rewrite Z.mul_0_r, Z.add_0_r in RD1 end;
    swto 1520;
    let FR1 := fresh "FR" in let FR2 := fresh "FR" in let cw := fresh "cw" in let cc := fresh "cc" in
    destruct (x1s_fr1520 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRA) as [FR1 (cw & cc & FR2)];
    replace (bv_unsigned sp + -240 + 32) with (bv_unsigned sp + -208) in FR2 by lia;
    rewrite ?sx32_small in FR2 by lia;
    eapply FIN; [ exact MU3 | exact WM2 | exact MI2 | exact SYA | exact FR1 | exact FR2 ].

  Hypothesis X1520 : forall m5 h ws rank tl rs rs2 syms jdt jsy j8 (c1 c2 cw cc x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11) = Ok (ws, rank, tl) ->
    tl <= mtl + 1 ->
    rank_start_loop (Z.to_nat (tl + 1)) 0 0 rank (repeat 0 13) = Ok rs ->
    sort_loop (Z.to_nat (hs_nbSymbols h)) 0 ws rs (repeat None 256) = Ok (rs2, syms) ->
    rw_cells usegs m5 DT [C4 (Z_to_bv 64 (mtl * 0x01000001 + tl * 65536))] ->
    u8arr usegs m5 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    u32arr usegs m5 W (map (Z_to_bv 64) rank) ->
    u8arr usegs m5 (W + 980) (omerge jsy syms) -> zlen jsy = 256 ->
    rw_cells usegs m5 (SP + -240) [C8 c1; C8 c2; CB 8 j8; C8 (Z_to_bv 64 (hs_ret h))] ->
    rw_cells usegs m5 (SP + -208) (x1_fr DT tl W (Z_to_bv 64 0) (Z_to_bv 64 (Znth 0 rank)) cw cc) ->
    rw_cells usegs m5 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m5 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m5 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m5 lo (SP + -240) ->
    munch WALL m m5 -> wmono usegs m m5 -> mem_inv usegs m5 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 (Z_to_bv 64 1) x12
                            (Z_to_bv 64 (W + 980)) x14 x15 (Z_to_bv 64 (2^64 - 1 - (W + 980))) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 1520)) fc None m5 (seg_rom usegs)).
  Lemma x1_1012 : forall m1 h ws rank tl rs rsw jrest jdt jsy j8 j16a j16b j16c j24 (c1 c2 x1 x6 x7 x11 x12 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11) = Ok (ws, rank, tl) ->
    tl <= mtl + 1 ->
    rank_start_loop (Z.to_nat (tl + 1)) 0 0 rank (repeat 0 13) = Ok rs ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 0x01000001 + tl * 65536))] ->
    u8arr usegs m1 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    u8arr usegs m1 (W + 1236) (map (Z_to_bv 8) ws ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 W (map (Z_to_bv 64) rank) ->
    u32arr usegs m1 (W + 52) rsw -> length rsw = 13%nat -> (forall i, 0 <= i <= tl -> nth_error rsw (Z.to_nat i) = Some (Z_to_bv 64 (Znth i rs))) ->
    u8arr usegs m1 (W + 980) jsy -> zlen jsy = 256 ->
    rw_cells usegs m1 (SP + -240) [C8 c1; C8 c2; CB 8 j8; C8 (Z_to_bv 64 (hs_ret h)); CB 16 j16a; C8 (Z_to_bv 64 DT);
                                   CB 16 j16b; C8 (Z_to_bv 64 (tl + 1)); CB 16 j16c; C8 (Z_to_bv 64 W); CB 24 j24] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -240) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp (Z_to_bv 64 (18446744073709551615 - (W + 52))) x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 W)
                            x11 x12 (Z_to_bv 64 (W + 980)) (Z_to_bv 64 (hs_nbSymbols h)) (Z_to_bv 64 tl)
                            (Z_to_bv 64 (W + 52)) (Z_to_bv 64 (hs_nbSymbols h + -4)) (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 W) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (mtl * 0x01000001)) x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 1012)) fc None m1 (seg_rom usegs)).
  Proof using All.
    intros m1 h ws rank tl rs rsw jrest jdt jsy j8 j16a j16b j16c j24 c1 c2 x1 x6 x7 x11 x12 x29 x30 x31
      RSt SOK RET1 SRCB MTL DT0 DTA DTL W0 WA WL LOS SPB SPA DJ RSC TLM RKS HDR DTa LJD HWr LJR RKr RSWa LRSW AGr SYa LSY
      FRa NSr TLr SVr ST MU WM MI.
    unfold hk in DJ. unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in MU.
    assert (P2 : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    destruct (rescale_spec _ _ _ _ (Z.min (mtl + 1) 11) (WF_of_stats h SOK) ltac:(lia)) as (ws' & rank' & tl' & RSC' & WF' & TLM').
    rewrite RSC in RSC'. injection RSC' as <- <- <-.
    pose proof WF' as (TLW & LWS & NBS & WSR & LRK & RKC & KS). unfold FseNCount.Zlength in LWS, LRK.
    unfold HufPure_HufStats.HUF_TABLELOG_MAX in TLW.
    destruct (x1_model_path mtl src h ws rank tl MTL SRCB RSt RSC TLM ltac:(lia)) as (rs' & rs2 & syms & cells & RSL & SRT & FWW & TOK & ZC & CV).
    rewrite RKS in RSL. injection RSL as <-.
    assert (LRS : zlen rs = 13) by (rewrite (x1s_rsl_len _ _ _ _ _ _ RKS), repeat_length; reflexivity).
    assert (RB0 : 0 <= Znth 0 rank <= 256)
      by (unfold Znth; exact (proj1 (Forall_nth (fun v => 0 <= v <= 256) rank) (wf_rank_bounds _ _ _ _ WF') 0%nat 0 ltac:(lia))).
    assert (LHW : length (map (Z_to_bv 8) ws ++ jrest) = 256%nat) by (rewrite length_app, length_map; lia).
    assert (FIN : forall m5 (cw cc y1 y5 y6 y7 y8 y10 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      munch [(W + 52, W + 52 + 52); (W + 980, W + 980 + 256); (SP + -208, SP + -112)] m1 m5 -> wmono usegs m1 m5 -> mem_inv usegs m5 ->
      u8arr usegs m5 (W + 980) (omerge jsy syms) ->
      rw_cells usegs m5 (SP + -240) [C8 c1; C8 c2; CB 8 j8; C8 (Z_to_bv 64 (hs_ret h))] ->
      rw_cells usegs m5 (SP + -208) (x1_fr DT tl W (Z_to_bv 64 0) (Z_to_bv 64 (Znth 0 rank)) cw cc) ->
      evt usegs POST (MS (mkR y1 (Z_to_bv 64 (SP + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (-9)) y10 (Z_to_bv 64 1) y12
                              (Z_to_bv 64 (W + 980)) y14 y15 (Z_to_bv 64 (2^64 - 1 - (W + 980))) y17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4))
                              (Z_to_bv 64 (-25)) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                         F (Z_to_bv 64 (PHUF_RDT_X1 + 1520)) fc None m5 (seg_rom usegs))).
    { intros m5 cw cc y1 y5 y6 y7 y8 y10 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 MU5 WM5 MI5 SY5 FR5 FW5.
      clear FRa RSWa SYa HWr.
      transport_after_call usegs m1 m5 MU5 WM5.
      eapply X1520 with (h := h) (ws := ws) (rank := rank) (tl := tl) (rs := rs) (rs2 := rs2) (syms := syms) (jdt := jdt) (jsy := jsy)
        (j8 := j8) (c1 := c1) (c2 := c2) (cw := cw) (cc := cc) (m5 := m5).
      all: first [ eassumption | lia | (unfold hk; lia) ]. }
    rewrite <- (omerge_none 256 jsy) in SYa.
    x1w_zbr. snorm. x1w_br BU.
    - assert (N4 : hs_nbSymbols h < 4) by lia. clear BU.
      swto 1328.
      eapply so1u with (m := m1) (ws := ws) (L := map (Z_to_bv 8) ws ++ jrest) (js := jsy) (FB := SP + -240) (W := W)
        (nbS := hs_nbSymbols h) (tl := tl) (r := hs_ret h) (DT := DT) (c1 := c1) (c2 := c2) (j8 := j8) (j16a := j16a)
        (j16b := j16b) (j16c := j16c) (j24 := j24) (k := Z.to_nat (hs_nbSymbols h)) (n := 0) (rs := rs) (syms := repeat None 256)
        (rsw := rsw) (r0 := (rs2, syms)) (m1 := m1);
        [ first [ eassumption | lia | (intros ?k ?Hk; apply x1s_nth; lia)
                 | (unfold so_inv; refine (conj RSWa (conj LRSW (conj AGr (conj LRS (conj SYa (conj (repeat_length _ _)
                      (conj HWr (conj FRa (conj _ (conj _ MI)))))))))); [apply munch_refl | apply wmono_refl]) ] .. | ].
      intros m3 rs3 syms3 rsw3 y6 y7 y28 E3 INV3. injection E3 as <- <-.
      x1s_tail INV3 FIN RKr.
    - assert (N4 : 4 <= hs_nbSymbols h) by lia. clear BU.
      swto 1036.
      eapply so4u with (m := m1) (ws := ws) (L := map (Z_to_bv 8) ws ++ jrest) (js := jsy) (FB := SP + -240) (W := W)
        (nbS := hs_nbSymbols h) (tl := tl) (r := hs_ret h) (DT := DT) (c1 := c1) (c2 := c2) (j8 := j8) (j16a := j16a)
        (j16b := j16b) (j16c := j16c) (j24 := j24) (k := Z.to_nat (hs_nbSymbols h)) (n := 0) (rs := rs) (syms := repeat None 256)
        (rsw := rsw) (r0 := (rs2, syms)) (m1 := m1);
        [ first [ eassumption | lia | (intros ?k ?Hk; apply x1s_nth; lia)
                 | (unfold so_inv; refine (conj RSWa (conj LRSW (conj AGr (conj LRS (conj SYa (conj (repeat_length _ _)
                      (conj HWr (conj FRa (conj _ (conj _ MI)))))))))); [apply munch_refl | apply wmono_refl]) ] .. | ].
      intros m2 n2 rs2' syms2 rsw2 y8 y29 y30 y31 N2 SL2 INV2.
      x1w_zbr. snorm. x1w_br BU2.
      + assert (N3 : n2 < hs_nbSymbols h) by lia. clear BU2.
        swto 1328.
        eapply so1u with (m := m1) (ws := ws) (L := map (Z_to_bv 8) ws ++ jrest) (js := jsy) (FB := SP + -240) (W := W)
          (nbS := hs_nbSymbols h) (tl := tl) (r := hs_ret h) (DT := DT) (c1 := c1) (c2 := c2) (j8 := j8) (j16a := j16a)
          (j16b := j16b) (j16c := j16c) (j24 := j24) (k := Z.to_nat (hs_nbSymbols h - n2)) (n := n2) (rs := rs2') (syms := syms2)
          (rsw := rsw2) (r0 := (rs2, syms)) (m1 := m2);
          [ first [ eassumption | lia | (intros ?k ?Hk; apply x1s_nth; lia) ] .. | ].
        intros m3 rs3 syms3 rsw3 y6 y7 y28 E3 INV3. injection E3 as <- <-.
        x1s_tail INV3 FIN RKr.
      + assert (N3 : n2 = hs_nbSymbols h) by lia. clear BU2. subst n2.
        rewrite Z.sub_diag in SL2. cbn [Z.to_nat sort_loop] in SL2. injection SL2 as <- <-.
        x1s_tail INV2 FIN RKr.
  Qed.
End TOP.
End CANSEC.
