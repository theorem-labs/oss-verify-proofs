(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Ju0MainEntry SymDriveH4
Ju0LibStdioCall Ju0OpenFail_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ju0MainEntryN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0Usage_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0LibStdioCall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0Usage_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."], [["1O"; "1Some"; "1cons"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "3Z"; "4ALU_ADD"]; ["4BC_GE"; "4BC_GEU"; "4BC_LT"; "4BC_NE"; "4M_MUL"; "5sc_f"; "5sc_fd"; "5sc_l"; "5sc_ret"; "5sc_s"; "5sc_wb"; "5sc_wp"; "5stdio_call"; "5stdio_res"; "6LX"; "6u_knE4"]; ["6u_knF3"; "6u_knG"; "6u_knG3"; "6u_knG4"; "6u_rA"; "6u_rB"; "6u_rC"; "6u_rD"; "6u_rE"; "6u_rE4"; "6u_rF"; "6u_rF3"; "6u_rF4"; "6u_rG"; "6u_rG3"; "6u_rG4"]; ["6u_rH"; "6u_rH3"; "6u_rH4"; "6u_scE4"; "6u_scF3"; "6u_scG"; "6u_scG3"; "6u_scG4"; "6u_srE4"; "6u_srF3"; "6u_srG"; "6u_srG3"; "6u_srG4"; "7EAlu"; "7EAluw"; "7EExt"]; ["7ELit"; "7EMd"; "7EVar"; "7SA"; "7SCBr"; "7SCReadBase"; "7expr"; "7s_pc"; "7scripts"; "7sidecond"; "7sym_state"]]).
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition u_ssA0 : sym_state := SS 0x33e1c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.
Definition u_ssB0 : sym_state := SS 0x9f468 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.
Definition u_ssC0 : sym_state := SS 0x9f468 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.
Definition u_ssD0 : sym_state := SS 0x9ffd8 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.
Definition u_ssE0 : sym_state := SS 0x9f468 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.
Definition u_ssF0 : sym_state := SS 0x9f468 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
Definition u_ssG0 : sym_state := SS 0x9f468 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
Definition u_ssH0 : sym_state := SS 0x9f938 u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.
Definition u_scrF3 : scripts := SCR [false] [] [].
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
Definition u_ssH30 : sym_state := SS 0x9f938 u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.
Definition u_scrE4 : scripts := SCR [true; false] [] [].
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
Definition u_ssG40 : sym_state := SS 0x9f468 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
Definition u_ssH40 : sym_state := SS 0x9f938 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.
Lemma u_itinerary : ltac2:(TCodec.tc2 tcn__Ju0Usage_defs "[E'<'='9'>'5'R9%211%5241(8&R7&4'R:%:216'R8&Q4%53321%635:1%811&:%138=4%<4A>31+eX]D(2(R4(;(C(R2u@%211(R0+2%211%948741(6%11M%=3N31%L4Q1N?1%Q43NA1&Q5%M3KJ1%N3MQ21%Q011%H3OQ43%Q34Q8Q521%Q44Q9Q6G:%Q<3Q621&Q6%Q53Q3Q21%Q63Q5Q:1%Q811%Q03Q7Q<3%Q;4Q@Q=21+e[U8%Q=4QBQ?1C%QE3Q?31&Q7%Q>3Q<Q;1%Q?3Q>QC1%QA11%Q93Q@QE3%QD4QIQF21(3(B(QN(?&Nz%Q611%53431%Q>48714(R5(R3(QMu1%Q@11%33;1:%521:%7414@:%QH3R91Q<%QI3R::1%R84R=R:QK1%R@3R:E1&Q8%R93R7R61%R:3R9R>1%R<11%R43R;R@3%R?4RDRA21(A+R9%QM11%R44R331J(@(QO(0u4%34R821O%Q23Q1MN%R;4R:621%R=3RN1R1%R>3RO91%RM4S2ROR@1%S53RO?1&Q:%RN3RLRK1%RO3RNS31%S111%RI3S0S53%S44S9S621(R1(D-1%RC11%4331Q@%Q:3QB1H+7%RG11%RN4RMM31%S03SA1RD%S?4SDSAS21%SG3SA<1&Q=%S@3S>S=1%SA3S@SE1%SC11%S;3SBSG3%SF4SKSH21+ckT<%SH4SMSJ1RN%T03SJ31'7'M%211&LuW6&QJ&Q1%43321(1&QE%2291%T<3941%T<2T;T;%T=21T<&H%116&E%118%T<4TATA31&F%11;%T?49TD31+cnYH+flQ@%TB4TGTG21%TC4=TH1SM%TK3=51'R6%TL211%TM212&J%11F&K%11H%TL47731&G%11K%TO49:31%T>1R:-a@%T=11%S33S;31%S43S<4S;-a2%TA11%S73S?31%U84CC51%U94CD1S>%UA3C;1&Q@%U:3U8U71%U;3U:U?1%U=11%U53U<UA3%U@4UEUB21+cVi4%UB4UGUD1TH%UJ3UD31&Q;%UC3UAU@1%UD3UCUH1%UF11%U>3UEUJ3%UI4UNUK21%U;4T5S:R@R>%U=3UN1U1%UL4V1UNR51%V43UN41uV6&QI&Q0%R43321&QD%R12R81%V;3R831%QM13%QL14%V74V<V<21%QK16%V94R3V>21+cnh8%V;4V@V@1QJ%V<4R6VA1UF%VD3R641%VD2QGQI%QG1=%QF1>%VA4QLQL21&I%11A%VD4QNQO31%QH1C%VF4QOR121-a9%V311%TI3U1QE1%VJ4R5R5QG1+RTU=%V711%VM4R7R831%VN4R7R91SB%W63A91&Q>%VO3VMVL1%W03VOW41%W211%VJ3W1W63%W54W:W721%W=3W71S>&QK&Q2%S<3S;21&QF%S92S@1%WC3S@31%S513%S414%W?4WDWD21%S316%WA4S;WF21%WI3S;1RO%RK19%RJ1:%WE4S0S021%RI1<%WG4S1S221%WH4S3S3RERE%WI4S3S41UN%X13S331&QA%WJ3WHWG1%WK3WJWO1%WM11%WE3WLX13%X04X5X221%X83X21R?&Q9%X13WOWN1%X23X1X61%X411%WL3X3X83%X74X<X921%WI4VCUHUFV?%WK3X<1U>%X:4X?X<TC1%XB3X<41uU6&QH&O%TB3321&QC%T?2TF1%XI3TF31%T;13%T:14%XE4XJXJ21%T916%XG4TAXL21+dQY8%XI4XNXN1T8%XJ4TDXO1X4%Y23TD41%T41<%T31=%XN4T9T921%R=1?%Y04T:T;21%T41A%Y24T;T=21%W33W;T3R;%Y44T?T?T11%Y54T?T@1W3%Y64T?TA1W=%Y>3RI51&Q<%Y73Y5Y41%Y83Y7Y<1%Y:11%Y23Y9Y>3%Y=4YBY?21%YE3Y?1X:&Q?%Y>3Y<Y;1%Y?3Y>YC1%YA11%Y93Y@YE3%YD4YIYF21%YL3YF1UM&QL&Q3%UK3UJ21&QG%UH2UO1%Z23UO31%UD13%UC14%YN4Z3Z321%UB16%Z04UJZ521%Z83UJ1U>%U:19%U91:%Z44U?U?21%U81<%Z64U@UA21%Z74UAUBQ3X<%Z?3UA21&QB%Z83Z6Z51%Z93Z8Z=1%Z;11%Z33Z:Z?3%Z>4ZCZ@21%ZF3Z@1TM%ZH281%ZI2@1%ZJ2G1%ZK2N1%ZL2Q61%ZM2Q>1%ZN2QK1%ZO2R51%[02R=1%[12RH1%[22S01%[32S91%[42S@1%[52SG1%[62SO1%[72TB1%[82TL1%[92U41%[:2U?1%[;2UI1%[<2V@1%[=2W01%[>2W=1%[?2WG1%[@2X:1%[A2Y01%[B2YL1%[C2Z61%[D2Z?1").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
