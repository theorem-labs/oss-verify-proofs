(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
Ltac2 kr_t_Sums_code () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63454K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63458K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr08c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_6345cK4ELinuxProcessSemantics5Riscv5Instr5instr06c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63460K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5instr07c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63464c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63468c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_6346cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63470K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5instr04c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63474c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634d0K4ELinuxProcessSemantics5Riscv5Instr5aluop09c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634d4K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634d8c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634dcc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634e0c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634e4c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634e8c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634ecc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634f0K4ELinuxProcessSemantics5Riscv5Instr5instr03c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634f4c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634f8c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_634fcK4ELinuxProcessSemantics5Riscv5Instr5instr09c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63500K4ELinuxProcessSemantics5Riscv5Instr5aluop03c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63504c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63508c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_6350cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63510c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63514c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63518c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_6351cK4ELinuxProcessSemantics5Riscv5Instr5msize04c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63520c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63524c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63528K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_6352cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a00c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a04c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a08c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a0cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a10c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a14c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a18K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a1cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a20c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a24c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a28c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a2cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a30c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a34c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a38c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a3cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a40c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a44c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a48c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a4cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a50c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a54c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a58c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a5cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a60c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a64c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a68c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a6cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a70c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a74K4ELinuxProcessSemantics5Riscv5Instr5aluop02c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a78c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a7cc5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a80c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a84c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a88c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a8cK4ELinuxProcessSemantics5Riscv5Instr5aluop05c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a90c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a94c5ARocqVerifyHarness?AgentSubmission2AS9BSum_code7W_63a98".
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_63454 : bv 32 := 0x02060063.
Lemma D_63454 : decode_any W_63454 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;Jg00<<R5#0R6#2#5R7%25#0R5#0#3g00<aR831g00===178%25#5%06R6#0#0#0#3;18C8%36C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63458 : bv 32 := 0x00c50633.
Lemma D_63458 : decode_any W_63458 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00?ej47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@Q#8R4P0P1g00AJg00<<R5#0R6#4R7#:R8%45#0#0#1g00<aR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6345c : bv 32 := 0x00050693.
Lemma D_6345c : decode_any W_6345c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Bb#9R4P0P1g00AJg00<<R5#0R6#2R7#5R8%25#0R5#2#3g00<aR931%07#3=189%05#5g00==;19C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63460 : bv 32 := 0x0005c703.
Lemma D_63460 : decode_any W_63460 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00C[j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00DG#9R4P0P1g00E@g00Elg00<<R5#0R6#1R7#5R8%15R5#1#0#3g00<aR932%17#3=289%05#0#5g00==;29D8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63464 : bv 32 := 0x00e68023.
Lemma D_63464 : decode_any W_63464 = Some (Store SZ1 13 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00FLj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00G8#9R4P0P1g00E@g00<<R5#0R6#1#5R7%15R5#0R8#1#3g00<aR932%15#0#3=279%08#5g00==;29C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63468 : bv 32 := 0x00168693.
Lemma D_63468 : decode_any W_63468 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00H1#9R4P0P1g00AJg00<<R5#0R6#1#5%15#0R7#1#2g00<aR833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6346c : bv 32 := 0x00158593.
Lemma D_6346c : decode_any W_6346c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Hj#9R4P0P1g00AJg00<<R5#0R6#1R7#5%17#2g00<aR733R8P8%15#0#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63470 : bv 32 := 0xfec698e3.
Lemma D_63470 : decode_any W_63470 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Ic#9R4P0P1g00J\g00<<R5#1R6#0#5R7%05R5#1R8#0R9#2g00<aR:33%18#2=37:%59%05#0#0#0#0#0#0#1#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63474 : bv 32 := 0x00008067.
Lemma D_63474 : decode_any W_63474 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00KNj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00L:#9R4P0P1g00<<R5#0R6#5#3R7g00==R8g00<aR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634d0 : bv 32 := 0x00a666b3.
Lemma D_634d0 : decode_any W_634d0 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj13Tg002mj1:Tg003Kj11Tg003ij32Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00M3#8R4P0P1g00Mlg00<<R5#0R6#3R7#:R8%35#0R5#3#1g00<aR932%05#1=289%07#1=289C7%06#1C6,52R634R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634d4 : bv 32 := 0x00f6f693.
Lemma D_634d4 : decode_any W_634d4 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00NX#9R4P0P1g00OQg00<<R5#1R6#0#5%05R5#1R7#0#2g00<aR833R9P9%17#5%05#0#2;38C8%16#2C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634d8 : bv 32 := 0x02068063.
Lemma D_634d8 : decode_any W_634d8 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00P=#9R4P0P1g00;Jg00<<R5#0R6#2#5R7%25#0#2R5#3g00<aR831g00===178%55%06R6#0#0#0#3;18C8%36C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634dc : bv 32 := 0x04060863.
Lemma D_634dc : decode_any W_634dc = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Q6#9R4P0P1g00;Jg00<<R5#0R6#2R7#5R8%25#0R5#0#3g00<aR931g00===189%25#5%07#0#0#0#3;19C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634e0 : bv 32 := 0x00c50633.
Lemma D_634e0 : decode_any W_634e0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00?ej47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Qo#8R4P0P1g00AJg00<<R5#0R6#4R7#:R8%45#0#0#1g00<aR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634e4 : bv 32 := 0x00050693.
Lemma D_634e4 : decode_any W_634e4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Rh#9R4P0P1g00AJg00<<R5#0R6#2R7#5R8%25#0R5#2#3g00<aR931%07#3=189%05#5g00==;19C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634e8 : bv 32 := 0x00b68023.
Lemma D_634e8 : decode_any W_634e8 = Some (Store SZ1 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00FLj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Sa#9R4P0P1g00E@g00<<R5#0R6#1R7#5R8%15#0R5#1#3g00<aR932%17#3=289%05#5g00==;29C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634ec : bv 32 := 0x00168693.
Lemma D_634ec : decode_any W_634ec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00TZ#9R4P0P1g00AJg00<<R5#0R6#1#5%15#0R7#1#2g00<aR833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634f0 : bv 32 := 0xfec69ce3.
Lemma D_634f0 : decode_any W_634f0 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00US#9R4P0P1g00J\g00<<R5#1R6#0#5R7%05R5#1R8#0R9#2g00<aR:33%18#2=37:%59%05#0#0#0#0#0#0#0#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634f4 : bv 32 := 0x0380006f.
Lemma D_634f4 : decode_any W_634f4 = Some (Jal 0 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00VLj28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00W8#9R4P0P1g00<<R5#0R6#1R7#5g00==g00<aR833%07#1#5%15#1#0#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634f8 : bv 32 := 0x02060a63.
Lemma D_634f8 : decode_any W_634f8 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00X1#9R4P0P1g00;Jg00<<R5#0R6#2#5R7%25#0R5#0#3g00<aR831g00===178%25R5#5%05#0#3;18C8%06#3C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_634fc : bv 32 := 0x00c50633.
Lemma D_634fc : decode_any W_634fc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00?ej47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Xj#8R4P0P1g00AJg00<<R5#0R6#4R7#:R8%45#0#0#1g00<aR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63500 : bv 32 := 0x00859693.
Lemma D_63500 : decode_any W_63500 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00Ycj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00ZO#9R4P0P1g00[Hg00<<R5#1R6#0R7#5R8%05#1R5#0#2g00<aR933%07#2=389%55%16R6#1#2;39C8%26C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63504 : bv 32 := 0x00b6e5b3.
Lemma D_63504 : decode_any W_63504 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00\4#8R4P0P1g00Mlg00<<R5#2R6#0R7#:R8%07#1g00<aR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63508 : bv 32 := 0x01059693.
Lemma D_63508 : decode_any W_63508 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Ycj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00\m#9R4P0P1g00[Hg00<<R5#0R6#1R7#5R8%15#0R5#1#2g00<aR933%17#2=389%55%06R6#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6350c : bv 32 := 0x00b6e5b3.
Lemma D_6350c : decode_any W_6350c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00]f#8R4P0P1g00Mlg00<<R5#2R6#0R7#:R8%07#1g00<aR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63510 : bv 32 := 0x02059693.
Lemma D_63510 : decode_any W_63510 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Ycj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00^_#9R4P0P1g00[Hg00<<R5#0R6#1R7#5R8%15#0R5#1#2g00<aR933%17#2=389%55%06R6#0#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63514 : bv 32 := 0x00b6e5b3.
Lemma D_63514 : decode_any W_63514 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00_X#8R4P0P1g00Mlg00<<R5#2R6#0R7#:R8%07#1g00<aR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63518 : bv 32 := 0x00050693.
Lemma D_63518 : decode_any W_63518 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00`Q#9R4P0P1g00AJg00<<R5#0R6#2R7#5R8%25#0R5#2#3g00<aR931%07#3=189%05#5g00==;19C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6351c : bv 32 := 0x00b6b023.
Lemma D_6351c : decode_any W_6351c = Some (Store SZ8 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00FLj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00aJ#9R4P0P1g00bCg00<<R5#0R6#1R7#5R8%15#0R5#1#3g00<aR932%17#3=289%05#5g00==;29C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63520 : bv 32 := 0x00b6b423.
Lemma D_63520 : decode_any W_63520 = Some (Store SZ8 13 11 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00FLj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00bo#9R4P0P1g00bCg00<<R5#0R6#1R7#5R8%15#0R5#1#2g00<aR933%17#2=389%05#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63524 : bv 32 := 0x01068693.
Lemma D_63524 : decode_any W_63524 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00ch#9R4P0P1g00AJg00<<R5#0R6#1#5%15#0R5#1#2g00<aR733R8P8%05#5%06R6#0#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63528 : bv 32 := 0xfec6eae3.
Lemma D_63528 : decode_any W_63528 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00da#9R4P0P1g00eZg00<<R5#1R6#0#5R7%05R5#1R8#0R9#2g00<aR:33%18#2=37:%59%05#0#0#0#0#0#0#1#0#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6352c : bv 32 := 0x00008067.
Lemma D_6352c : decode_any W_6352c = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00KNj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00fL#9R4P0P1g00<<R5#0R6#5#3R7g00==R8g00<aR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a00 : bv 32 := 0xff010113.
Lemma D_63a00 : decode_any W_63a00 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00gE#9R4P0P1g00AJg00<<R5#1R6#0#5%26g00<aR733R8P8%05R5#1#1#5%05#0#0#0#0#0#1#1#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a04 : bv 32 := 0x00113423.
Lemma D_63a04 : decode_any W_63a04 = Some (Store SZ8 2 1 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00FLj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00h>#9R4P0P1g00bCg00<<R5#0R6#5#3R7%16g00<aR832%15=278%55#0#0#3%06R6#0#1;28C8%16C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a08 : bv 32 := 0x00058693.
Lemma D_63a08 : decode_any W_63a08 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00i7#9R4P0P1g00AJg00<<R5#0R6#1R7#5R8%15#0R5#1#3g00<aR932%17#3=289%05#5g00==;29C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a0c : bv 32 := 0x00100713.
Lemma D_63a0c : decode_any W_63a0c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00j0#9R4P0P1g00AJg00<<R5#0R6#2#5R7%25R8#2#0#3g00<aR931g00===179%08#0#5%35;19C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a10 : bv 32 := 0x02871713.
Lemma D_63a10 : decode_any W_63a10 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Ycj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00ji#9R4P0P1g00[Hg00<<R5#0R6#1R7#5%15R5#1#0#2g00<aR833R9P9%05#5%07#0#0#2;38C8%06#2C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a14 : bv 32 := 0x00170593.
Lemma D_63a14 : decode_any W_63a14 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00kb#9R4P0P1g00AJg00<<R5#0R6#1R7#5R8%17#2g00<aR733%15R9#1#0#2=387%09#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a18 : bv 32 := 0x08b6f263.
Lemma D_63a18 : decode_any W_63a18 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00l[#9R4P0P1g00mTg00<<R5#0R6#1R7#5R8%15#0#1R5#2g00<aR933%17#2=389%55%06R6#0#0#1#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a1c : bv 32 := 0x00000593.
Lemma D_63a1c : decode_any W_63a1c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00nF#9R4P0P1g00AJg00<<R5#0R6#2R7#5R8%27#3g00<aR731g00==R9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a20 : bv 32 := 0x00d50733.
Lemma D_63a20 : decode_any W_63a20 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00o?#8R4P0P1g00AJg00<<R5#0R6#2R7#:R8%25R5#2#0#1g00<aR933%07#1=389%05#2#1=389C7%06#1C6,52R634R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a24 : bv 32 := 0x00750793.
Lemma D_63a24 : decode_any W_63a24 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0108#9R4P0P1g00AJg00<<R5#0R6#1R7#5R8%15R5#1R9#1#2g00<aR:33%07#2=38:%05#0#5%29;3:C8%06#2C7,62R634R:P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a28 : bv 32 := 0xff87f793.
Lemma D_63a28 : decode_any W_63a28 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0111#9R4P0P1g00OQg00<<R5#1R6#0#5%05R5#0#0R7#2g00<aR833R9P9%15#1#5%07#0#0#0#0#1#1#1#2;38C8%16#2C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a2c : bv 32 := 0xff877613.
Lemma D_63a2c : decode_any W_63a2c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g011j#9R4P0P1g00OQg00<<R5#1R6#0#5R7%05R5#1#1R8#2g00<aR933%05R5#1#2=379%58%05#0#0#0#0#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a30 : bv 32 := 0x02f57463.
Lemma D_63a30 : decode_any W_63a30 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g012c#9R4P0P1g00mTg00<<R5#0R6#1R7#5R8%07R7#2g00<aR933%15R5#1#1#2=389%05#1#5%07#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a34 : bv 32 := 0x02068263.
Lemma D_63a34 : decode_any W_63a34 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g013\#9R4P0P1g00;Jg00<<R5#0R6#1#5R7%15#0#1R5#3g00<aR832g00===278%55%06R6#1#0#0#3;28C8%36C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a38 : bv 32 := 0x00000593.
Lemma D_63a38 : decode_any W_63a38 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g014U#9R4P0P1g00AJg00<<R5#0R6#2R7#5R8%27#3g00<aR731g00==R9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a3c : bv 32 := 0x00150693.
Lemma D_63a3c : decode_any W_63a3c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g015N#9R4P0P1g00AJg00<<R5#0R6#3R7#5R8%35#0R9#3#1g00<aR:32%07#1=28:%09#5%15;2:C8%06#1C7,62R634R:P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a40 : bv 32 := 0x00068813.
Lemma D_63a40 : decode_any W_63a40 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g016G#9R4P0P1g00AJg00<<R5#0R6#2#5R7%06R6#0#0#3g00<aR831%25#0R5#2#3=178%05#5g00==;18C8%36C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a44 : bv 32 := 0xfff6c683.
Lemma D_63a44 : decode_any W_63a44 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj12Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00C[j59Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=1g009GR0g00:3R1'CR2#BR3g017@#:R4P0P1g00E@g00Elg00<<R5#2R6#0#6%05R5#2R7#0#3g00<aR834R9P9%27#6%15#1#1#1#1#3;48D9%26#3C7,82R635R8P3P3%A3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_63a48 : bv 32 := 0x00d5e5b3.
Lemma D_63a48 : decode_any W_63a48 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0189#8R4P0P1g00Mlg00<<R5#2R6#0R7#:R8%07#1g00<aR733R9P9%05#2#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a4c : bv 32 := 0x00f87663.
Lemma D_63a4c : decode_any W_63a4c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0192#9R4P0P1g00mTg00<<R5#0R6#1#5R7%06R6#0#0#2g00<aR833%15R5#1#1#2=378%05R5#1#5%05#2;38C8%26C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a50 : bv 32 := 0x00180693.
Lemma D_63a50 : decode_any W_63a50 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g019k#9R4P0P1g00AJg00<<R5#0R6#3#5R7%35#0R8#3#1g00<aR932%06R6#0#0#1=279%08#5%15;29C8%16C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a54 : bv 32 := 0xfee866e3.
Lemma D_63a54 : decode_any W_63a54 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01:d#9R4P0P1g00eZg00<<R5#1R6#0#5R7%16R6#1#1#2g00<aR833%05R5#0R9#1#2=378%15#0#5%09#0#0#0#0#1#0#0#1#1#2;38C8%26C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a58 : bv 32 := 0x00c7fa63.
Lemma D_63a58 : decode_any W_63a58 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01;]#9R4P0P1g00mTg00<<R5#0R6#1R7#5R8%15R5#1#1#2g00<aR933%05R5#0#2=389%15#5%07#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a5c : bv 32 := 0x0007b683.
Lemma D_63a5c : decode_any W_63a5c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00C[j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01<V#9R4P0P1g00bCg00?ER5g00<<R6#1R7#0#5R8%06R6#1R9#0#3g00<aR:32%06#0#3=28:%19#5g00==;2:D8%17#3C7,62R734R:P3P3%:3P0g00=[P1g00>LC@,?2P4P7E<R7g00>eR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a60 : bv 32 := 0x00878793.
Lemma D_63a60 : decode_any W_63a60 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01=O#9R4P0P1g00AJg00<<R5#0R6#1#5%15R5#1#1#2g00<aR733R8P8%05#0#5%06R6#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a64 : bv 32 := 0x00b6e5b3.
Lemma D_63a64 : decode_any W_63a64 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01>H#8R4P0P1g00Mlg00<<R5#2R6#0R7#:R8%07#1g00<aR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a68 : bv 32 := 0xfec7eae3.
Lemma D_63a68 : decode_any W_63a68 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01?A#9R4P0P1g00eZg00<<R5#1R6#0#5R7%05R5#0#0R8#2g00<aR933%15R5#1#2=379%05#5%08#0#0#0#0#1#0#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a6c : bv 32 := 0x02a66063.
Lemma D_63a6c : decode_any W_63a6c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01@:#9R4P0P1g00eZg00<<R5#0R6#3R7#5R8%35#0R5#0#1g00<aR932%07#1=289%35#5%06R6#0#0#0#1;29C8%16C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a70 : bv 32 := 0x00e67e63.
Lemma D_63a70 : decode_any W_63a70 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01A3#9R4P0P1g00mTg00<<R5#0R6#1#5R7%15R5#0R8#0#2g00<aR933%15#0R5#2=379%18#5%05#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a74 : bv 32 := 0x40c70733.
Lemma D_63a74 : decode_any W_63a74 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00?ej47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Al#8R4P0P1g01Beg00<<R5#0R6#2#:R7%25R5#2#0#1g00<aR833R9P9%05#0#1=378C7%06#1C6,52R634R8P3P3%93P0g00=[P1g00>LC@,?2P4P6E;R6g00>eR4g00?ER2'<1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a78 : bv 32 := 0x00064503.
Lemma D_63a78 : decode_any W_63a78 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00C[j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01CQ#9R4P0P1g00E@g00Elg00<<R5#0R6#5R7#3R8%07#2g00<aR731%55#0#0R5#2=187%35g00==;17D8%06#2C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a7c : bv 32 := 0xfff70713.
Lemma D_63a7c : decode_any W_63a7c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00B6j49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=2g009GR0g00:3R1'CR2#BR3g01DJ#:R4P0P1g00AJg00<<R5#1R6#0#6%05R5#0R7#1#3g00<aR834R9P9%15#1#6%07#2#2#2#2#3;48C9%16#3C7,82R635R8P3P3%A3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_63a80 : bv 32 := 0x00a5e5b3.
Lemma D_63a80 : decode_any W_63a80 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj11Tg002Hj14Tg002mj1:Tg003Kj10Tg003ij32Tg00?ej47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01EC#8R4P0P1g00Mlg00<<#1R5#4R6#:R7%46#0g00<aR832R9P9%16#0=278C7%15#0C6,52R533R8P3P3%93P0g00=[P1g00>LC@,?2P4P5E;R5g00>eR4g00?ER2'<1=85=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a84 : bv 32 := 0x00160613.
Lemma D_63a84 : decode_any W_63a84 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01F<#9R4P0P1g00AJg00<<R5#0R6#5#3%55#0#0R7#1g00<aR832R9P9%37%15;28C8%06#1C7,62R634R8P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a88 : bv 32 := 0xfe0718e3.
Lemma D_63a88 : decode_any W_63a88 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01G5#9R4P0P1g00J\g00<<R5#1R6#0#5R7%05R5#0R8#1#3g00<aR932g00===279%15#0#5%08#0#0#0#0#0#1#1#1#1#3;29C8%16#3C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a8c : bv 32 := 0x0015b513.
Lemma D_63a8c : decode_any W_63a8c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Gn#9R4P0P1g01Hgg00<<R5#0R6#3R7#5R8%07#1g00<aR932%37#1=289%35#0#0#5%15;29C8%06#1C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a90 : bv 32 := 0x00813083.
Lemma D_63a90 : decode_any W_63a90 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00C[j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01IS#9R4P0P1g00bCg00?ER5g00<<R6#0R7#5#3R8%16g00<aR932%17=289%56#0#0#3%07R7#0#1;29D8%17C7,62R734R9P3P3%:3P0g00=[P1g00>LC@,?2P4P7E<R7g00>eR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a94 : bv 32 := 0x01010113.
Lemma D_63a94 : decode_any W_63a94 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00B6j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01JL#9R4P0P1g00AJg00<<R5#0R6#5#3%16g00<aR732R8P8%55#0#0#3%06R6#0#0#1;27C8%16C7,62R634R7P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_63a98 : bv 32 := 0x00008067.
Lemma D_63a98 : decode_any W_63a98 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00KNj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01KE#9R4P0P1g00<<R5#0R6#5#3R7g00==R8g00<aR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=[P1g00>LC@,?2P4P6E<R6g00>eR4g00?ER2';1=96=442d3>o"). Qed.
