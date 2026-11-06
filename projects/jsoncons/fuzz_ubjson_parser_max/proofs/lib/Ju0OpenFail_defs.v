(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import RunEnv
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Ju0MainEntry SymDriveH4 Ju0LibStdioCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ju0OpenFail_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0LibStdioCall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0OpenFail_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."], [["1O"; "1Some"; "1cons"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "3Z"; "4ALU_ADD"]; ["4BC_GE"; "4BC_GEU"; "4BC_LT"; "4BC_LTU"; "4M_MUL"; "5sc_f"; "5sc_fd"; "5sc_l"; "5sc_ret"; "5sc_s"; "5sc_wb"; "5sc_wp"; "5stdio_call"; "5stdio_res"; "6PX"; "6knF4"]; ["6knG3"; "6knH"; "6knH3"; "6knH4"; "6rA"; "6rB"; "6rC"; "6rD"; "6rE"; "6rF"; "6rF4"; "6rG"; "6rG3"; "6rG4"; "6rH"; "6rH3"]; ["6rH4"; "6rI"; "6rI3"; "6rI4"; "6scF4"; "6scG3"; "6scH3"; "6scH4"; "6scOF"; "6srF4"; "6srG3"; "6srH"; "6srH3"; "6srH4"; "7EAlu"; "7EAluw"]; ["7EExt"; "7ELit"; "7EMd"; "7EVar"; "7SA"; "7SCBr"; "7SCReadBase"; "7expr"; "7s_pc"; "7scripts"; "7sidecond"; "7sym_state"]]).
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS : list Z := [0xaa1b4; 0xaa734; 0xaaca8; 0xaa0b8; 0x992d4; 0x99460; 0x9d38c; 0x99b24; 0x9ec8c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
match stdio_call nv sr kn with
| Some r => r
| None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
end.
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition IHI : Z := 0xea000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.
Definition ssA0 : sym_state := SS 0x33e1c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
KRange (EVar 2) 0x7fff80000000 0x800000400000
:: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0xab160 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
Definition logM1 : list sentry :=
[SE (SA (EVar 0) (-544)) 1 (ELit 32);
SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.
Definition ssC0 : sym_state := SS 0x9f468 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.
Definition ssD0 : sym_state := SS 0x9f468 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.
Definition ssE0 : sym_state := SS 0x9ffd8 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.
Definition ssF0 : sym_state := SS 0x9f468 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.
Definition ssG0 : sym_state := SS 0x9f468 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.
Definition ssH0 : sym_state := SS 0x9f468 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.
Definition ssI0 : sym_state := SS 0x9f938 srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.
Definition scrG3 : scripts := SCR [false] [] [].
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
Definition ssI30 : sym_state := SS 0x9f938 srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.
Definition scrF4 : scripts := SCR [true; false] [] [].
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
Definition ssH40 : sym_state := SS 0x9f468 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
Definition ssI40 : sym_state := SS 0x9f938 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.
Lemma itinerary_63_64 : ltac2:(TCodec.tc2 tcn__Ju0OpenFail_defs "X6'<'='9'>'5'R:%211%5241(8&R8&4'R;%:216'R9&Q<%53321%635:1%811&:%138=4%<4A>31+ckT<(2(R5(3(A(QN(?(R2(D(R1-1%211&N%63521+QO%611%;3:31+1%911%A4@?31(6%11Q5%E3Q631%Q44Q9Q6G1%Q<3Q6I1'7'M%211&LuV7&QJ&Q0%43321(1&QE%2291%QH3941%QH2QGQG%QI21QH&H%116&E%118%QH4QMQM31&F%11;%QK49R031+cnh8+flQ@%QN4R3R321+2%R04>R521%R83>61'R7%R9211%R:212%R;213&J%11H&K%11J%R:48831&I%11M%R=4:;31&G%11Q0%R@4<>31(R3(0%211-a@%QO11%R43R331%R53R44QN-`O%R311%R83R731%RK4II51+RZiN%R711%RN4KL31%RO4KM1R0%S73K@1&Q?%S03RNRM1%S13S0S51%S311%RK3S2S73%S64S;S821%S74S<S9RJR5%S?3S921uW7&QL&Q2%R33321&QF%R02R71%SF3R731%QL13%QK14%SB4SGSG21%QJ16%SD4R2SI21+cnYH%SF4SKSK1QI%SG4R5SL1QH%SO3R541%QC1<%QB1=%SK4QIQI21%Q>1?%SM4QJQK21%SN4QLQLQ8Q8z%S:11%T14QNQO31%T93QN51&QB%T23T0SO1%T33T2T71%T511%SM3T4T93%T84T=T:21+cVi4%T:4T?T<1S8%TB3T<31&Q:%T;3T9T81%T<3T;T@1%T>11%T63T=TB3%TA4TFTC21%T34T2T1SFSI(;(@(R0u4%244R51SN(QO%13T6T0I%23T71J%T<48741%T>3TO1SJ%T?3U0;1%TN4U3U0TA1%U63U0>1uU7&QI&O%SJ3321&QD%SG2SN1%U=3SN31%SC13%SB14%U94U>U>21%SA16%U;4SIU@21+dQY8%U=4UBUB1S@%U>4SLUC1S?%UF3SL41%S:1<%S91=%UB4S@S@21%S81?%UD4SASB21%S71A%UF4SBSD21%U53U4S4RN%UH4SFSFS21u2%S911%UK4SHSI31%UL4SHSJ1U3%V43SH71&Q=%UM3UKUJ1%UN3UMV21%V011%UH3UOV43%V34V8V521+eX]D%V54V:V71U3%V=3V731&Q@%V63V4V31%V73V6V;1%V911%V13V8V=3%V<4VAV>21%VD3V>1S6&QM&Q3%U73S721&QG%U42U;1%VJ3U;31%U013%TO14%VF4VKVK21%TN16%VH4U6VM21%W03U61S2%TD19%TC1:%VL4TJTJ21%T?1<%VN4TKTL21-a?%V:11%V?3V>T>1%W24U0U0T<1%W34U0U11S3%W;3U061&QC%W43W2W11%W53W4W91%W711%VO3W6W;3%W:4W?W<21%WB3W<1S1%WD281%WE2D1%WF2K1%WG2Q21%WH2Q:1%WI2QD1%WJ2R31%WK2R=1%WL2RE1%WM2S:1%WN2SD1%WO2SO1%X02T91%X12TA1%X22TJ1%X32UJ1%X42V;1%X52VH1").
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma itinerary_le62 : ltac2:(TCodec.tc2 tcn__Ju0OpenFail_defs "VC'<'='9'>'5'R:%211%5241(8&R8&4'R;%:216'R9&Q4%53321%635:1%811&:%138=4%<4A>31+e\ZL(6%11B%@4EB31%H3B51&Q5%A3?>1%B3AF1%D11%<3CH3%G4LI21+eX]D(2(R5(3(C(QO(?(R3uQ6%211(R1z%211%83741+_ooooooooolP1%511%>4=<31%@3Q<1J%Q:4Q?Q<B1%QB3Q<D1&Q6%Q;3Q9Q81%Q<3Q;Q@1%Q>11%Q63Q=QB3%QA4QFQC21%QB4QGQDJQ3%QJ3QD21&Q7%QC3QAQ@1%QD3QCQH1%QF11%Q>3QEQJ3%QI4QNQK21+e[U8%QK4R0QM1Q<%R33QM31&Q8%QL3QJQI1%QM3QLR11%QO11%QG3QNR33%R24R7R421(B&N%Q83Q71Q1%Q<4Q;312(R6(R4(QNu2%Q<11%33Q>18%521Q:u1%8421QDQ;%QG3RC1R1%QH3RD;1%RB4RGRDQJ1%RJ3RDA1&Q9%RC3RAR@1%RD3RCRH1%RF11%R>3RERJ3%RI4RNRK21(;(A+QO%QK11%R44431J(@(R0(0u4%34921O%R73R6OR0%R;4;621%R=3S91RG%R>3S:91%S84S=S:R@1%S@3S:@1&Q;%S93S7S61%S:3S9S>1%S<11%S43S;S@3%S?4SDSA21(R2(D-1%RA11%4331Q@%Q<3RG1H+1%RE11%RN4NM31%S03SL1S:%SJ4SOSLS21%T23SL<1&Q>%SK3SISH1%SL3SKT01%SN11%SF3SMT23%T14T6T321+ckT<%T34T8T51SD%T;3T531'7'M%211&LuW7&QK&Q1%43321(1&QH%2291%TG3941%TG2TFTF%TH21TG&H%116&E%118%TG4TLTL31&F%11;%TJ49TO31+cnYH+flQ@%TM4U2U221+2%TO4>U421%U73>61'R7%U8211%U9212&J%11G&K%11I%U847731&G%11L%U;49:31%T=1R;-a@%T<11%S63TA31%S73TB4S<-`N%T@11%S:3TE31%UD4CC51%UE4CD1TA%UM3C;1&QA%UF3UDUC1%UG3UFUK1%UI11%UA3UHUM3%UL4V1UN21+cVi4%UN4V3V01U?%V63V031%V82:1%V92Q11%V:2QB1%V;2QO1%V<2R91%V=2RL1%V>2SC1%V?2T;1%V@2TE1%VA2TN1%VB2UI1").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
