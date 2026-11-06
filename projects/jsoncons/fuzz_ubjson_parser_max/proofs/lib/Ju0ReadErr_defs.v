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
Ltac2 tcn__Ju0ReadErr_defs () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0LibStdioCall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ju0ReadErr_defs.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."], [["1O"; "1Some"; "1cons"; "1false"; "1fst"; "1list"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "3Z"; "4ALU_ADD"]; ["4BC_GE"; "4BC_GEU"; "4BC_LT"; "4M_MUL"; "5sc_f"; "5sc_fd"; "5sc_l"; "5sc_ret"; "5sc_wb"; "5sc_wp"; "5stdio_call"; "5stdio_res"; "6PX"; "6knH"; "6rB"; "6rC"]; ["6rD"; "6rE"; "6rF"; "6rG"; "6rH"; "6rI"; "6scRE"; "6srH"; "7EAlu"; "7EAluw"; "7EExt"; "7ELit"; "7EMd"; "7EVar"; "7SA"; "7SCBr"]; ["7SCReadBase"; "7expr"; "7s_pc"; "7scripts"; "7sidecond"; "7sym_state"]]).
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition STOPS : list Z := [0xaa1b4; 0xaa734; 0xaaca8; 0xaa0b8; 0x992d4; 0x99460; 0x9d38c; 0x99b24; 0x9ec8c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition IHI : Z := 0xea000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition srRE_base : list expr :=
[ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0xc8cb0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.
Definition knRE0 : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
KWr (SA (EVar 0) (-8388608)) 8388608;
KRange (EVar 2) 0x7fff80000000 0x800000400000;
KWr (SA (ELit 0) 0xb6000) 0x34000;
KImg 0x10000 0xb7230; KImg 0xb7231 0xb7279; KImg 0xc7279 0xc8be0; KImg 0xe8cb8 0xe8cd8;
KWord (SA (ELit 0) 0xc8be8) 8 (ELit 0xc8be8);
KWord (SA (ELit 0) 0xc8c08) 4 (EVar 5);
KImg 0xc8c14 0xc8c60; KImg 0xc8c68 0xc8c80; KImg 0xc8c88 0xc8ca0;
KImg 0xc8cb0 0xc8cc0; KImg 0xc8cc8 0xe8cb8; KImg 0xe8cf0 0xe8f20;
KBlob (SA (ELit 0) 0xe8f20) (ELit 8) 2;
KImg 0xe8f28 0xe8f30; KImg 0xe8f41 0xe8f48; KImg 0xe8f50 0xe8f58; KImg 0xe8f68 0xe8f70;
KWord (SA (ELit 0) 0xe8f70) 8 (ELit 4096);
KImg 0xe8f78 0xe8fa8;
KImg 0xe9478 0xea000;
KRange (EVar 5) 1 4194303].
Definition ssB0 : sym_state := SS 0x34048 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
Definition logM1 : list sentry :=
[SE (SA (EVar 0) (-542)) 1 (ELit 32);
SE (SA (EVar 0) (-544)) 2 (ELit 28271);
SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
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
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.
Definition ssG0 : sym_state := SS 0x9f468 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.
Definition ssH0 : sym_state := SS 0x9f468 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
Definition scRE : stdio_res := Eval vm_compute in
match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.
Lemma itinerary_re : ltac2:(TCodec.tc2 tcn__Ju0ReadErr_defs "V0'<'='9'>'5'QD%211%5241(8&QB&4'QE%:216'QC&N%53321%635:1%811&:%138=4%<4A>31+eX]D(6%11B%@4EB31%H3B51&O%A3?>1%B3AF1%D11%<3CH3%G4LI21%O3I18&Q0%H3FE1%I3HM1%K11%C3JO3%N4Q3Q021+e[U8%Q04Q5Q21A%Q83Q231&Q1%Q13ON1%Q23Q1Q61%Q411%L3Q3Q83%Q74Q<Q921(2(Q?(3(B(Q9(?&L(Q;z%211%63541%:49815(Q@(Q>(Q8(Q=u2%211%43=1<%621;u1%9421C<%F3R11Q?%G3R2<1%R04R5R2QC1%R83R2J1&Q2%R13QOQN1%R23R1R61%R411%QL3R3R83%R74R<R921(;(A+QM%L11%Q34431N(@(Q:(0u4%34921Q3%Q63Q5Q0Q1%Q:4;621%Q<3RG1R5%Q=3RH91%RF4RKRHR91%RN3RH@1&Q3%RG3RERD1%RH3RGRL1%RJ11%RB3RIRN3%RM4S2RO21(Q<(C-1%QB11%4331QD%Q=3QF1H+1%QF11%QM4NM31%QO3S:1RH%S84S=S:RK1%S@3S:<1&Q4%S93S7S61%S:3S9S>1%S<11%S43S;S@3%S?4SDSA21+ckT<%SA4SFSC1S2%SI3SC31'7'K%211&JuW7&Q7&M%43321(1&Q6%2291%T53941%T52T4T4%T621T5&G%116&D%118%T54T:T:31&E%11;%T849T=31+cnYH+flQ@%T;4T@T@21+2%T=4>TB21%TE3>61'QA%TF211%TG212&H%11G&I%11I%TF47731&F%11L%TI49:31%S31R;-a@%S=11%S73S@31%S83SA4S@-`L%SA11%S;3SD31%U24CC51%U34CD1SB%U;3C;1&Q5%U43U2U11%U53U4U91%U711%TO3U6U;3%U:4U?U<21+cVi4%U<4UAU>1TM%UD3U>31%UF2:1%UG2Q11%UH2QB1%UI2QO1%UJ2R91%UK2RL1%UL2SC1%UM2TD1%UN2TN1%UO2U61").
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
