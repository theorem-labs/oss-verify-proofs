(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Sums2_code () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_638fcK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr08c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63900K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63904K4ELinuxProcessSemantics5Riscv5Instr5instr06c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63908K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_6390cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63910c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63914K4ELinuxProcessSemantics5Riscv5Instr5instr07c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63918c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_6391cK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63920c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63924K4ELinuxProcessSemantics5Riscv5Instr5instr0=c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63928K4ELinuxProcessSemantics5Riscv5Instr5aluop02c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_6392cK4ELinuxProcessSemantics5Riscv5Instr5aluop09c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63930K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63934c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63938c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_6393cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63940c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63944c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63948K4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_6394cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63950c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63954c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63958K4ELinuxProcessSemantics5Riscv5Instr5msize04c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_6395cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63960c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63964K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5instr04c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_63968c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50fe0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50fe4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50fe8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50fecc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50ff0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50ff4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50ff8K4ELinuxProcessSemantics5Riscv5Instr5instr09c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_50ffcK4ELinuxProcessSemantics5Riscv5Instr5aluop03c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51000c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51004K4ELinuxProcessSemantics5Riscv5Instr5msize03c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51008c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5100cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51010K4ELinuxProcessSemantics5Riscv5Instr5aluop07c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51014c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51018c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5101cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51020K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51024c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51028c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5102cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51030c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51034c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51038c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5103cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51040c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51044c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51048c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5104cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51050c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51054c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51058c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5105cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51060c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51064c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51068c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5106cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51070c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51074c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51078c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5107cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51080c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51084c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51088c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5108cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51090c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51094c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51098c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5109cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510a0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510a4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510a8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510acc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510b0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510b4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510b8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510bcc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510c0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510c4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510c8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510ccc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510d0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510d4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510d8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510dcc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510e0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510e4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510e8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510ecc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510f0c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510f4c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510f8c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_510fcc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51100c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51104c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51108c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5110cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51110c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51114c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51118c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5111cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51120c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51124c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51128c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_5112cc5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51130c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51134c5ARocqVerifyHarness?AgentSubmission2AS:BSum2_code7W_51138".
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_638fc : bv 32 := 0x06060663.
Lemma D_638fc : decode_any W_638fc = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;Kg00<=R5#0R6#1#5R7%15#0R5#0#3g00<bR832g00=>=278%15R5#5%15#0#0#3;28C8%06#3C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63900 : bv 32 := 0x00000693.
Lemma D_63900 : decode_any W_63900 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@R#9R4P0P1g00ALg00<=R5#0R6#2#5R7%25#0R5#2#3g00<bR831g00=>R9=178%05#5?198C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63904 : bv 32 := 0x00d58733.
Lemma D_63904 : decode_any W_63904 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Bd#8R4P0P1g00ALg00<=R5#2R6#0R7#:R8%05R5#0#2#1g00<bR933%07#1=389%25#0#1=389C7%26#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63908 : bv 32 := 0x00074703.
Lemma D_63908 : decode_any W_63908 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00DJ#9R4P0P1g00EDg00F0g00<=R5#0R6#1#5%15R5#1#0#3g00<bR732R8P8%05#0#5g00=>;27D8%06#3C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6390c : bv 32 := 0x00070c63.
Lemma D_6390c : decode_any W_6390c = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00FP#9R4P0P1g00;Kg00<=R5#0R6#1#5R7%15R5#1#0#3g00<bR832g00=>=278%05R5#1#5%05#0#3;28C8%06#3C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63910 : bv 32 := 0x00d507b3.
Lemma D_63910 : decode_any W_63910 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00GJ#8R4P0P1g00ALg00<=R5#2R6#0R7#:R8%05R5#0#0#1g00<bR933%27#1=389%25#0#1=389C7%26#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63914 : bv 32 := 0x00168693.
Lemma D_63914 : decode_any W_63914 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00HD#9R4P0P1g00ALg00<=R5#0R6#1#5%15#0R7#1#2g00<bR833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63918 : bv 32 := 0x00e78023.
Lemma D_63918 : decode_any W_63918 = Some (Store SZ1 15 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Ij#9R4P0P1g00EDg00<=R5#0R6#1#5R7%15R5#1R8#1#3g00<bR932%08#3=279%05#0#5g00=>;29C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6391c : bv 32 := 0xfed614e3.
Lemma D_6391c : decode_any W_6391c = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Jd#9R4P0P1g00K^g00<=R5#1R6#0#5R7%05R5#1R8#1#2g00<bR933%08R8#2=379%58%05#0#0#0#0#0#1#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63920 : bv 32 := 0x00060693.
Lemma D_63920 : decode_any W_63920 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00LP#9R4P0P1g00ALg00<=R5#0R6#2#5R7%25#0R5#2#3g00<bR831%05R5#3=178%55g00=>;18C8%06#3C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63924 : bv 32 := 0x00d505b3.
Lemma D_63924 : decode_any W_63924 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00MJ#8R4P0P1g00ALg00<=R5#0R6#2R7#:R8%27#1g00<bR933%07#1=389%25#0#2#1=389C7%06#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63928 : bv 32 := 0x40d6073b.
Lemma D_63928 : decode_any W_63928 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00NDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00O0#8R4P0P1g00Ojg00<=R5#0R6#2#:R7%25R5#2#0#1g00<bR833%05R5#0#1=378%25#1=378C7%06#1C6,52R634R8P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6392c : bv 32 := 0x00b76733.
Lemma D_6392c : decode_any W_6392c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00PV#8R4P0P1g00QPg00<=R5#2R6#0R7#:R8%05#0#2#1g00<bR533R9P9%07#1=385C7%26#1C6,52R634R5P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=56=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63930 : bv 32 := 0x00f77713.
Lemma D_63930 : decode_any W_63930 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00R<#9R4P0P1g00S6g00<=R5#0R6#1#5%15R5#1R7#0#2g00<bR833R9P9%05#0#5%17#2;38C8%06#2C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63934 : bv 32 := 0x00070e63.
Lemma D_63934 : decode_any W_63934 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Sb#9R4P0P1g00;Kg00<=R5#0R6#1#5R7%15R5#1#0R8#3g00<bR932g00=>=279%05#1#5%08#3;29C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63938 : bv 32 := 0x02d60863.
Lemma D_63938 : decode_any W_63938 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00T\#9R4P0P1g00;Kg00<=R5#0R6#3#5R7%35#0R5#0R8#1g00<bR932%35R5#1=279%55%08#0#1;29C8%06#1C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6393c : bv 32 := 0x00c50633.
Lemma D_6393c : decode_any W_6393c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00B8j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00UV#8R4P0P1g00ALg00<=R5#0R6#4R7#:R8%45#0#0#1g00<bR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63940 : bv 32 := 0x00058023.
Lemma D_63940 : decode_any W_63940 = Some (Store SZ1 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00VP#9R4P0P1g00EDg00<=R5#0R6#2R7#5R8%27#3g00<bR731g00=>R9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63944 : bv 32 := 0x00158593.
Lemma D_63944 : decode_any W_63944 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00WJ#9R4P0P1g00ALg00<=R5#0R6#1R7#5%17#2g00<bR733R8P8%15#0#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63948 : bv 32 := 0xfec59ce3.
Lemma D_63948 : decode_any W_63948 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00XD#9R4P0P1g00K^g00<=R5#1R6#0R7#5R8%07#2g00<bR733%05R5#1R9#1#2=387%09#5%05#0#0#0#0#0#0#0#1#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6394c : bv 32 := 0x01c0006f.
Lemma D_6394c : decode_any W_6394c = Some (Jal 0 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00Y>j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Yj#9R4P0P1g00<=R5#0R6#1R7#5g00=>g00<bR833%07#1#5%15#1#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63950 : bv 32 := 0x00d60c63.
Lemma D_63950 : decode_any W_63950 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Zd#9R4P0P1g00;Kg00<=R5#0R6#3#5R7%35#0R5#0R8#1g00<bR932%35R5#1=279%55%08#1;29C8%06#1C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63954 : bv 32 := 0x00c50633.
Lemma D_63954 : decode_any W_63954 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00B8j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00[^#8R4P0P1g00ALg00<=R5#0R6#4R7#:R8%45#0#0#1g00<bR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63958 : bv 32 := 0x0005b023.
Lemma D_63958 : decode_any W_63958 = Some (Store SZ8 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00\X#9R4P0P1g00]Rg00<=R5#0R6#2R7#5R8%27#3g00<bR731g00=>R9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6395c : bv 32 := 0x0005b423.
Lemma D_6395c : decode_any W_6395c = Some (Store SZ8 11 0 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00^>#9R4P0P1g00]Rg00<=R5#0R6#2R7#5R8%27#3g00<bR731g00=>=187%25#0#0#5%06R6#0#3;17C8%36C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63960 : bv 32 := 0x01058593.
Lemma D_63960 : decode_any W_63960 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00_8#9R4P0P1g00ALg00<=R5#0R6#1R7#5%17#2g00<bR733R8P8%15#0#0#5%06R6#0#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63964 : bv 32 := 0xfec5eae3.
Lemma D_63964 : decode_any W_63964 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00`2#9R4P0P1g00`lg00<=R5#1R6#0R7#5R8%07#2g00<bR733%05R5#1R9#1#2=387%09#5%05#0#0#0#0#0#0#1#0#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63968 : bv 32 := 0x00008067.
Lemma D_63968 : decode_any W_63968 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00a^j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00bJ#9R4P0P1g00<=R5#0R6#5#3R7g00=>R8g00<bR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.



(* [comment removed for export] *)
Definition W_50fe0 : bv 32 := 0x00200613.
Lemma D_50fe0 : decode_any W_50fe0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00cD#9R4P0P1g00ALg00<=R5#0R6#5#3R7%55#0#0R5#2g00<bR831g00=>=178%35%26;18C8%06#2C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50fe4 : bv 32 := 0x14c5ea63.
Lemma D_50fe4 : decode_any W_50fe4 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00d>#9R4P0P1g00`lg00<=R5#0R6#1R7#5R8%17#2g00<bR933%15#0R5#0#2=389%15#5%07#1#0#1#0#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50fe8 : bv 32 := 0x00100613.
Lemma D_50fe8 : decode_any W_50fe8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00e8#9R4P0P1g00ALg00<=R5#0R6#5#3R7%55#0#0R8#2g00<bR931g00=>=179%38%25;19C8%06#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50fec : bv 32 := 0x00100693.
Lemma D_50fec : decode_any W_50fec = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00f2#9R4P0P1g00ALg00<=R5#0R6#2#5R7%25#0R8#2#3g00<bR931g00=>=179%08#5%35;19C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50ff0 : bv 32 := 0x00c0006f.
Lemma D_50ff0 : decode_any W_50ff0 = Some (Jal 0 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00Y>j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00fl#9R4P0P1g00<=R5#0R6#1R7#5g00=>g00<bR833%07#1#5%15#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50ff4 : bv 32 := 0x00160613.
Lemma D_50ff4 : decode_any W_50ff4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00gf#9R4P0P1g00ALg00<=R5#0R6#5#3%55#0#0R7#1g00<bR832R9P9%37%15;28C8%06#1C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50ff8 : bv 32 := 0x12b60c63.
Lemma D_50ff8 : decode_any W_50ff8 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00h`#9R4P0P1g00;Kg00<=R5#1R6#0R7#5R8%05#1R5#1#2g00<bR933%07#2=389%05#5%16R6#0#0#0#1#1#1#2;39C8%26C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_50ffc : bv 32 := 0x00461713.
Lemma D_50ffc : decode_any W_50ffc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00jF#9R4P0P1g00k@g00<=R5#0R6#2#5R7%25R5#2#0#3g00<bR831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51000 : bv 32 := 0x00e50733.
Lemma D_51000 : decode_any W_51000 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00kl#8R4P0P1g00ALg00<=R5#0R6#2R7#:R8%25#2#0#1g00<bR533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51004 : bv 32 := 0x00072703.
Lemma D_51004 : decode_any W_51004 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00lf#9R4P0P1g00m`g00?FR5g00<=R6#0R7#1#5%16R6#1#0#3g00<bR832R9P9%06#0#5g00=>;28D8%07#3C7,62R734R8P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51008 : bv 32 := 0x00060893.
Lemma D_51008 : decode_any W_51008 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00nL#9R4P0P1g00ALg00<=R5#0R6#2#5R7%06R6#0#2#3g00<bR831%25#0#0R5#3=178%55g00=>;18C8%36C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5100c : bv 32 := 0xfff88793.
Lemma D_5100c : decode_any W_5100c = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj12Tg002mj16Tg003Kj13Tg003ij34Tg00?fj49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#2#2p=0g009GR0g00:3R1'CR2#BR3g00oF#:R4P0P1g00ALg00<=R5#1R6#2#6R7%25R5#0R8#3g00<bR934%16R6#1#2#3=479%15#1#6%08#0#0#0#3;49C9%36C7,82R635R9P3P3%A3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2'=1>96=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_51010 : bv 32 := 0x0017d813.
Lemma D_51010 : decode_any W_51010 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g010@#9R4P0P1g011:g00<=R5#0R6#1#5R7%06R6#0#0#2g00<bR833%15R9#1#1#2=378%09#5%25;38C8%26C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51014 : bv 32 := 0x00481293.
Lemma D_51014 : decode_any W_51014 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g011f#9R4P0P1g00k@g00<=R5#0R6#5R7#3R8%27g00<bR731%06R6#0#0#2=187%55#0#3%26R6;17C8P6C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51018 : bv 32 := 0x005502b3.
Lemma D_51018 : decode_any W_51018 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j15Tg001cj11Tg002Hj1@Tg002mj18Tg003Kj10Tg003ij32Tg00B8j46Tg0058j47Tg005Xj24Tg006:j33j19Tg006Tj4?Tg0072j2:Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g012`#5R4P0P1g00ALg00<=#1R5#@R6#8R7%06g00<bR832R9%16#0=278P9C6%15#0C7,42R533R9P3P3%93P0g00=\P1g00>MC?,:2P4P5E;R5g00>fR4g00?FR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5101c : bv 32 := 0x0002a303.
Lemma D_5101c : decode_any W_5101c = Some (Load SZ4 true 6 5 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g013Z#9R4P0P1g00m`g00?FR5g00<=R6#0R7#5R8#3R9%56#0R6#2g00<bR:31%28=19:%06#3g00=>;1:D8%07#2C7,62R734R:P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51020 : bv 32 := 0xfce37ae3.
Lemma D_51020 : decode_any W_51020 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g014T#9R4P0P1g015Ng00<=R5#1R6#0#5R7%05R5#1R8#2g00<bR933%05R5#1#2=379%08#5%05#0#0#0#1#0#1#0#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51024 : bv 32 := 0x0002b303.
Lemma D_51024 : decode_any W_51024 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g016@#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#5R8#3R9%56#0R6#2g00<bR:31%28=19:%06#3g00=>;1:D8%07#2C7,62R734R:P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51028 : bv 32 := 0x00489893.
Lemma D_51028 : decode_any W_51028 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g017:#9R4P0P1g00k@g00<=R5#0R6#1#5%06R6#0#1#3g00<bR732R8P8%15#0#5%36R6;27C8P6C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5102c : bv 32 := 0x011508b3.
Lemma D_5102c : decode_any W_5102c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00B8j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0184#8R4P0P1g00ALg00<=#0R5#4R6#:R7%05R5#0#4#1g00<bR832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00=\P1g00>MC@,?2P4P5E;R5g00>fR4g00?FR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51030 : bv 32 := 0x0048a383.
Lemma D_51030 : decode_any W_51030 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g018n#9R4P0P1g00m`g00?FR5g00<=R6#0R7#1#5R8%16R6#1#3g00<bR932%07R7#0#1#3=289%06#0#5%37R7;29D8P7C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51034 : bv 32 := 0x0068b023.
Lemma D_51034 : decode_any W_51034 = Some (Store SZ8 17 6 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g019h#9R4P0P1g00]Rg00<=R5#0R6#2#5R7%06R6#0#2#3g00<bR831%25#0R5#3=178%05#5g00=>;18C8%36C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51038 : bv 32 := 0x0082b303.
Lemma D_51038 : decode_any W_51038 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01:b#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#5R8#3R9%56#0R6#1g00<bR:32%18=29:%06#3%07R7#0#1;2:D8%17C7,62R734R:P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5103c : bv 32 := 0x0088be03.
Lemma D_5103c : decode_any W_5103c = Some (Load SZ8 true 28 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01;\#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#1#5R8%16R6#1#0#0#2g00<bR933%07R7#0R:#1#2=389%06#0#5%2:;39D8%27C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51040 : bv 32 := 0x0068b423.
Lemma D_51040 : decode_any W_51040 = Some (Store SZ8 17 6 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01<V#9R4P0P1g00]Rg00<=R5#0R6#3#5R7%06R6#0R8#3#1g00<bR932%35#0R5#1=279%05#5%18;29C8%16C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51044 : bv 32 := 0x00e2a023.
Lemma D_51044 : decode_any W_51044 = Some (Store SZ4 5 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01=P#9R4P0P1g00m`g00<=R5#0R6#2R7#5R8%37g00<bR731%25R5#2#0#3=187%05#0#5g00=>;17C8%06#3C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51048 : bv 32 := 0x0072a223.
Lemma D_51048 : decode_any W_51048 = Some (Store SZ4 5 7 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01>J#9R4P0P1g00m`g00<=R5#0R6#2R7#5R8%37g00<bR731%25R5#2#3=187%05#0#5%06#3R6;17C8P6C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5104c : bv 32 := 0x01c2b423.
Lemma D_5104c : decode_any W_5104c = Some (Store SZ8 5 28 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01?D#9R4P0P1g00]Rg00<=R5#0R6#3R7#5R8%17g00<bR732%35R5#3#0#0#1=287%05#0#5%06R6#0#1;27C8%16C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51050 : bv 32 := 0x00080893.
Lemma D_51050 : decode_any W_51050 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01@>#9R4P0P1g00ALg00<=R5#0R6#2#5R7%06R6#0R8#2#3g00<bR931%08#3=179%25#0#0#5g00=>;19C8%36C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51054 : bv 32 := 0xfaf6ece3.
Lemma D_51054 : decode_any W_51054 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01A8#9R4P0P1g00`lg00<=R5#1R6#0#5R7%05R5#1#0R8#2g00<bR933%05#0R5#2=379%58%05#0#1#0#0#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51058 : bv 32 := 0xf9dff06f.
Lemma D_51058 : decode_any W_51058 = Some (Jal 0 2097052, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj12Tg002mj14Tg003ij36Tg003Kj13Tg00Y>j29Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#2#2p=0g009GR0g00:3R1'CR2#BR3g01B2#:R4P0P1g00<=R5#1R6#2R7#4g00=>g00<bR836%17#2#4%25#0#0#0#0#0#0#1#1#2#0#1#1#3;68'9%16#3C7,82R635R8P3P3%A3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_5105c : bv 32 := 0x00000613.
Lemma D_5105c : decode_any W_5105c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Bl#9R4P0P1g00ALg00<=R5#0R6#5#2R7%55#0#0R5#3g00<bR831g00=>R9=178%25?198C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51060 : bv 32 := 0x00459693.
Lemma D_51060 : decode_any W_51060 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Cf#9R4P0P1g00k@g00<=R5#1R6#0R7#5R8%05#1R5#0#3g00<bR932%07#3=289%55%16#3R6;29C8P6C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51064 : bv 32 := 0x00d506b3.
Lemma D_51064 : decode_any W_51064 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01D`#8R4P0P1g00ALg00<=R5#0R6#2R7#:R8%25#0#2#1g00<bR533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51068 : bv 32 := 0x0006b703.
Lemma D_51068 : decode_any W_51068 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01EZ#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#1#5R8%16R6#1#0#3g00<bR932%06R6#1#3=289%06#5g00=>;29D8%07#3C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5106c : bv 32 := 0x0086b783.
Lemma D_5106c : decode_any W_5106c = Some (Load SZ8 true 15 13 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01FT#9R4P0P1g00]Rg00?FR5g00<=R6#1R7#0#5R8%06R6#0#0#2g00<bR933%16R6#0#2=389%16#5%17R7#1#2;39D8%27C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51070 : bv 32 := 0x00053803.
Lemma D_51070 : decode_any W_51070 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01GN#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#5R8#3R9%07R7#0#0#2g00<bR:31%08#2=19:%56#0#0#3g00=>;1:D8%27C7,62R734R:P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51074 : bv 32 := 0x00853883.
Lemma D_51074 : decode_any W_51074 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01HH#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#3R8#5R9%07R7#0R:#3#1g00<bR;32%08#1=29;%36#0#0#5%1:;2;D8%17C7,62R734R;P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=;7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51078 : bv 32 := 0x00e53023.
Lemma D_51078 : decode_any W_51078 = Some (Store SZ8 10 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01IB#9R4P0P1g00]Rg00<=R5#0R6#2R7#5R8%07#3g00<bR731%25R5#2#0#3=187%05#0#5g00=>;17C8%06#3C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5107c : bv 32 := 0x00f53423.
Lemma D_5107c : decode_any W_5107c = Some (Store SZ8 10 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01J<#9R4P0P1g00]Rg00<=R5#0R6#1R7#5R8%07#2g00<bR733%15R5#1#1#2=387%05#0#5%06R6#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51080 : bv 32 := 0x0106b023.
Lemma D_51080 : decode_any W_51080 = Some (Store SZ8 13 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01K6#9R4P0P1g00]Rg00<=R5#0R6#2#5R7%25#0R5#2#3g00<bR831%06R6#0#0#3=178%05#5g00=>;18C8%36C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51084 : bv 32 := 0x0116b423.
Lemma D_51084 : decode_any W_51084 = Some (Store SZ8 13 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01L0#9R4P0P1g00]Rg00<=R5#0R6#1#5R7%15#0R5#1#2g00<bR833%06R6#0R9#1#2=378%05#5%29;38C8%26C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51088 : bv 32 := 0x00000693.
Lemma D_51088 : decode_any W_51088 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Lj#9R4P0P1g00ALg00<=R5#0R6#2#5R7%25#0R5#2#3g00<bR831g00=>R9=178%05#5?198C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5108c : bv 32 := 0x00161793.
Lemma D_5108c : decode_any W_5108c = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Md#9R4P0P1g00k@g00<=R5#1R6#0#5R7%05R8#0#0#2g00<bR933%18R8#1#2=379%58%25;39C8%16#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51090 : bv 32 := 0x00178813.
Lemma D_51090 : decode_any W_51090 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01N^#9R4P0P1g00ALg00<=R5#0R6#1#5R7%06R6#0#0#2g00<bR833%15R9#1#1#2=378%09#0#5%25;38C8%26C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51094 : bv 32 := 0x00461713.
Lemma D_51094 : decode_any W_51094 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01OX#9R4P0P1g00k@g00<=R5#0R6#2#5R7%25R5#2#0#3g00<bR831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51098 : bv 32 := 0x00b86a63.
Lemma D_51098 : decode_any W_51098 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01PR#9R4P0P1g00`lg00<=R5#0R6#1R7#5R8%06R6#0#0#2g00<bR933%17#2=389%15#0#1#5%07#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5109c : bv 32 := 0x00278793.
Lemma D_5109c : decode_any W_5109c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01QL#9R4P0P1g00ALg00<=R5#1R6#0#5%05R5#0#0#2g00<bR733R8P8%15#1#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510a0 : bv 32 := 0x02b7ea63.
Lemma D_510a0 : decode_any W_510a0 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01RF#9R4P0P1g00`lg00<=R5#1R6#0R7#5R8%05R5#0#0#2g00<bR933%07#2=389%15#0R5#5%15#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510a4 : bv 32 := 0x04c69c63.
Lemma D_510a4 : decode_any W_510a4 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01S@#9R4P0P1g00K^g00<=R5#0R6#1R7#5R8%15#0R5#1R9#2g00<bR:33%05#2=38:%59%17#0#0#0#2;3:C8%06#2C7,62R634R:P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510a8 : bv 32 := 0x0880006f.
Lemma D_510a8 : decode_any W_510a8 = Some (Jal 0 136, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00Y>j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01T:#9R4P0P1g00<=#0R5#1R6#5g00=>g00<bR733%06#1#5%05R5#0#1#0#0#0#2;37'8%25C7,62R534R7P3P3%:3P0g00=\P1g00>MC@,?2P4P5E<R5g00>fR4g00?FR2';1=75=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510ac : bv 32 := 0x00e506b3.
Lemma D_510ac : decode_any W_510ac = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01U4#8R4P0P1g00ALg00<=R5#0R6#2R7#:R8%25R5#0#2#1g00<bR933%07#1=389%25#0#1=389C7%06#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510b0 : bv 32 := 0x00481893.
Lemma D_510b0 : decode_any W_510b0 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Un#9R4P0P1g00k@g00<=R5#0R6#2#5R7%06R6#0R8#2#3g00<bR931%08#3=179%25#0#5%36R6;19C8P6C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510b4 : bv 32 := 0x011508b3.
Lemma D_510b4 : decode_any W_510b4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00B8j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Vh#8R4P0P1g00ALg00<=#0R5#4R6#:R7%05R5#0#4#1g00<bR832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00=\P1g00>MC@,?2P4P5E;R5g00>fR4g00?FR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510b8 : bv 32 := 0x0006a683.
Lemma D_510b8 : decode_any W_510b8 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Wb#9R4P0P1g00m`g00?FR5g00<=R6#0R7#1#5%16#0R6#1#3g00<bR832R9P9%06#5g00=>;28D8%07#3C7,62R734R8P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510bc : bv 32 := 0x0008a883.
Lemma D_510bc : decode_any W_510bc = Some (Load SZ4 true 17 17 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01X\#9R4P0P1g00m`g00?FR5g00<=R6#0R7#1#5%07R7#0#1#3g00<bR832R9P9%16#0#0#5g00=>;28D8%37C7,62R734R8P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510c0 : bv 32 := 0x0116e463.
Lemma D_510c0 : decode_any W_510c0 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01YV#9R4P0P1g00`lg00<=R5#1R6#0#5R7%05#1#0R5#2g00<bR833%16R6#1R9#0#2=378%55%29;38C8%26C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510c4 : bv 32 := 0x00060813.
Lemma D_510c4 : decode_any W_510c4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01ZP#9R4P0P1g00ALg00<=R5#0R6#5#3R7%06R6#0#0#2g00<bR831%55#0#0R5#2=178%35g00=>;18C8%26C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510c8 : bv 32 := 0x00080693.
Lemma D_510c8 : decode_any W_510c8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01[J#9R4P0P1g00ALg00<=R5#0R6#2#5R7%25#0R5#2#3g00<bR831%06R6#0#0#3=178%05#5g00=>;18C8%36C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510cc : bv 32 := 0x00278793.
Lemma D_510cc : decode_any W_510cc = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01\D#9R4P0P1g00ALg00<=R5#1R6#0#5%05R5#0#0#2g00<bR733R8P8%15#1#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510d0 : bv 32 := 0xfcb7fae3.
Lemma D_510d0 : decode_any W_510d0 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01]>#9R4P0P1g015Ng00<=R5#1R6#0R7#5R8%05R5#0#0R9#2g00<bR:33%07#2=38:%15#0#5%09#0#0#1#0#1#0#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510d4 : bv 32 := 0x00469813.
Lemma D_510d4 : decode_any W_510d4 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01^8#9R4P0P1g00k@g00<=R5#0R6#2#5R7%06R6#0#0#3g00<bR831%25#0R5#2#3=178%55%36R6;18C8P6C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510d8 : bv 32 := 0x00479893.
Lemma D_510d8 : decode_any W_510d8 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01_2#9R4P0P1g00k@g00<=R5#1R6#0#5R7%16R6#1#0#3g00<bR832%05R5#0#0#3=278%15#5%36R6;28C8P6C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510dc : bv 32 := 0x01050833.
Lemma D_510dc : decode_any W_510dc = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j15Tg001cj10Tg002Hj1@Tg002mj18Tg003Kj11Tg003ij32Tg00B8j46Tg0058j47Tg005Xj24Tg006:j33j19Tg006Tj4?Tg0072j2:Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01_l#5R4P0P1g00ALg00<=#0R5#@R6#8R7%05R5#0#0#1g00<bR832R9%06#1=278P9C6%15C7,42R533R9P3P3%93P0g00=\P1g00>MC?,:2P4P5E;R5g00>fR4g00?FR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510e0 : bv 32 := 0x011508b3.
Lemma D_510e0 : decode_any W_510e0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00B8j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01`f#8R4P0P1g00ALg00<=#0R5#4R6#:R7%05R5#0#4#1g00<bR832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00=\P1g00>MC@,?2P4P5E;R5g00>fR4g00?FR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510e4 : bv 32 := 0x00082803.
Lemma D_510e4 : decode_any W_510e4 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003Kj13Tg003ij31Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01a`#9R4P0P1g00m`g00?FR5g00<=R6#0R7#5#2%07R7#0#0#3g00<bR831R9P9%56#0#0#2g00=>;18D8%37C7,62R734R8P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510e8 : bv 32 := 0x0008a883.
Lemma D_510e8 : decode_any W_510e8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01bZ#9R4P0P1g00m`g00?FR5g00<=R6#0R7#1#5%07R7#0#1#3g00<bR832R9P9%16#0#0#5g00=>;28D8%37C7,62R734R8P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510ec : bv 32 := 0x01186463.
Lemma D_510ec : decode_any W_510ec = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01cT#9R4P0P1g00`lg00<=R5#0R6#1#5R7%06R6#0R8#0#2g00<bR933%18#2=379%15#0#1#5%28;39C8%26C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510f0 : bv 32 := 0x00068793.
Lemma D_510f0 : decode_any W_510f0 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01dN#9R4P0P1g00ALg00<=R5#1R6#0#5R7%05R5#0#0#3g00<bR832%15R5#0#3=278%15#5g00=>;28C8%16#3C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510f4 : bv 32 := 0x00078693.
Lemma D_510f4 : decode_any W_510f4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01eH#9R4P0P1g00ALg00<=R5#1R6#0#5R7%05R5#1R8#0#3g00<bR932%05#0#3=279%18#5g00=>;29C8%16#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510f8 : bv 32 := 0x02c78c63.
Lemma D_510f8 : decode_any W_510f8 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01fB#9R4P0P1g00;Kg00<=R5#0R6#1#5R7%15R5#1R8#1#2g00<bR933%05R5#0#2=379%15#5%08#0#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_510fc : bv 32 := 0x00469613.
Lemma D_510fc : decode_any W_510fc = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00iZj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01g<#9R4P0P1g00k@g00<=R5#0R6#2#5R7%25#0R5#0#3g00<bR831%25#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51100 : bv 32 := 0x00c50633.
Lemma D_51100 : decode_any W_51100 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00B8j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01h6#8R4P0P1g00ALg00<=R5#0R6#4R7#:R8%45#0#0#1g00<bR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51104 : bv 32 := 0x00063783.
Lemma D_51104 : decode_any W_51104 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01i0#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#1#5R8%16R6#1#1#3g00<bR932%06#0R6#3=289%56g00=>;29D8%07#3C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51108 : bv 32 := 0x00e50733.
Lemma D_51108 : decode_any W_51108 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00B8j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01ij#8R4P0P1g00ALg00<=R5#0R6#2R7#:R8%25#2#0#1g00<bR533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00=\P1g00>MC@,?2P4P6E;R6g00>fR4g00?FR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5110c : bv 32 := 0x00073803.
Lemma D_5110c : decode_any W_5110c = Some (Load SZ8 true 16 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01jd#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#2#5R8%07R7#0#0#3g00<bR931%26R6#2#0#3=189%06#0#5g00=>;19D8%37C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51110 : bv 32 := 0x00873883.
Lemma D_51110 : decode_any W_51110 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01k^#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#1#5R8%07R7#0R9#1#2g00<bR:33%16R6#1#0#2=38:%06#0#5%29;3:D8%27C7,62R734R:P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51114 : bv 32 := 0x00f73023.
Lemma D_51114 : decode_any W_51114 = Some (Store SZ8 14 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01lX#9R4P0P1g00]Rg00<=R5#0R6#1#5R7%15R5#1R8#0#3g00<bR932%18#3=279%05#0#5g00=>;29C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51118 : bv 32 := 0x00863783.
Lemma D_51118 : decode_any W_51118 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00C^j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01mR#9R4P0P1g00]Rg00?FR5g00<=R6#0R7#1#5R8%16R6#1#1#2g00<bR933%06#0R6#2=389%56%07R7#0#2;39D8%27C7,62R734R9P3P3%:3P0g00=\P1g00>MC@,?2P4P7E<R7g00>fR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5111c : bv 32 := 0x00f73423.
Lemma D_5111c : decode_any W_5111c = Some (Store SZ8 14 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01nL#9R4P0P1g00]Rg00<=R5#0R6#1#5R7%15R5#1R8#0#2g00<bR933%18#2=379%05#0#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51120 : bv 32 := 0x01063023.
Lemma D_51120 : decode_any W_51120 = Some (Store SZ8 12 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01oF#9R4P0P1g00]Rg00<=R5#0R6#5#3R7%55#0#0R5#2g00<bR831%06R6#0#0#2=178%35g00=>;18C8%26C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51124 : bv 32 := 0x01163423.
Lemma D_51124 : decode_any W_51124 = Some (Store SZ8 12 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00I>j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g020@#9R4P0P1g00]Rg00<=R5#0R6#3#5R7%35#0#0R5#1g00<bR832%06R6#0R9#3#1=278%55%19;28C8%16C7,62R634R8P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51128 : bv 32 := 0x00068613.
Lemma D_51128 : decode_any W_51128 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?fj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g021:#9R4P0P1g00ALg00<=R5#0R6#2#5R7%25#0R5#0R8#3g00<bR931%25#3=179%58g00=>;19C8%06#3C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5112c : bv 32 := 0xf6b6e0e3.
Lemma D_5112c : decode_any W_5112c = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0224#9R4P0P1g00`lg00<=R5#1R6#0R7#5R8%05R5#1#0R9#2g00<bR:33%07#2=38:%59%05#0#0#1#0#0#1#1#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51130 : bv 32 := 0xfff58593.
Lemma D_51130 : decode_any W_51130 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj12Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00?fj49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=1g009GR0g00:3R1'CR2#BR3g022n#:R4P0P1g00ALg00<=R5#2R6#0R7#6%07#3g00<bR734R8P8%05R5#2#2#6%15#1#1#1#1#3;47C9%26#3C7,82R635R7P3P3%A3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2'=1>76=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_51134 : bv 32 := 0xf20594e3.
Lemma D_51134 : decode_any W_51134 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g023h#9R4P0P1g00K^g00<=R5#0R6#1R7#5R8%17#3g00<bR732g00=>=287%15R5#0#1#5%15#1#1#0#0#1#0#1#0#0#0#3;27C8%06#3C7,62R634R7P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_51138 : bv 32 := 0x00008067.
Lemma D_51138 : decode_any W_51138 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00a^j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g024b#9R4P0P1g00<=R5#0R6#5#3R7g00=>R8g00<bR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=\P1g00>MC@,?2P4P6E<R6g00>fR4g00?FR2';1=96=442d3>o"). Qed.
