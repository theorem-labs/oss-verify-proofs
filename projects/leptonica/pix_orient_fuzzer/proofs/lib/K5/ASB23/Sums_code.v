(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Sums_code () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f65cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f660C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr08c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f664C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f668C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5instr07c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f66cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f670C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f674C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f678C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5instr04c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f67cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6d8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6dcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6e0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6e4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6e8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6ecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6f0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6f4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6f8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f6fcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f700C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f704C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f708C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f70cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f710C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f714C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f718C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f71cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f720C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f724C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f728C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f72cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f730C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c69OSSVerify5KrLib2K55ASB239Sums_code7W_6f734C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc08C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc0cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc10C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc14C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc18C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc1cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc20C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc24C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc28C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc2cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc34C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc38C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc3cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc44C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc48C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc4cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc50C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc54C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc58C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc5cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc60C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc68C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc6cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc70C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc74C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc78C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc7cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc80C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc84C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc88C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc8cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc90C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc94C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc98C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fc9cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB239Sums_code7W_6fca0C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6f65c : bv 32 := 0x02060063.
Lemma D_6f65c : decode_any W_6f65c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;Pg00<BR5#0R6#2#5R7%25#0R5#0#3g00<gR831g00=C=178%25#5%06R6#0#0#0#3;18C8%36C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f660 : bv 32 := 0x00c50633.
Lemma D_6f660 : decode_any W_6f660 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00?kj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@W#8R4P0P1g00AVg00<BR5#0R6#4R7#:R8%45#0#0#1g00<gR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f664 : bv 32 := 0x00050693.
Lemma D_6f664 : decode_any W_6f664 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Bn#9R4P0P1g00AVg00<BR5#0R6#2R7#5R8%25#0R5#2#3g00<gR931%07#3=189%05#5g00=C;19C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f668 : bv 32 := 0x0005c703.
Lemma D_6f668 : decode_any W_6f668 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00Cmj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00DY#9R4P0P1g00EXg00FDg00<BR5#0R6#1R7#5R8%15R5#1#0#3g00<gR932%17#3=289%05#0#5g00=C;29D8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f66c : bv 32 := 0x00e68023.
Lemma D_6f66c : decode_any W_6f66c = Some (Store SZ1 13 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00Fdj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00GP#9R4P0P1g00EXg00<BR5#0R6#1#5R7%15R5#0R8#1#3g00<gR932%15#0#3=279%08#5g00=C;29C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f670 : bv 32 := 0x00168693.
Lemma D_6f670 : decode_any W_6f670 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00HO#9R4P0P1g00AVg00<BR5#0R6#1#5%15#0R7#1#2g00<gR833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f674 : bv 32 := 0x00158593.
Lemma D_6f674 : decode_any W_6f674 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00IN#9R4P0P1g00AVg00<BR5#0R6#1R7#5%17#2g00<gR733R8P8%15#0#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f678 : bv 32 := 0xfec698e3.
Lemma D_6f678 : decode_any W_6f678 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00JM#9R4P0P1g00KLg00<BR5#1R6#0#5R7%05R5#1R8#0R9#2g00<gR:33%18#2=37:%59%05#0#0#0#0#0#0#1#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f67c : bv 32 := 0x00008067.
Lemma D_6f67c : decode_any W_6f67c = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00L>j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Lj#9R4P0P1g00<BR5#0R6#5#3R7g00=CR8g00<gR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6d8 : bv 32 := 0x00a666b3.
Lemma D_6f6d8 : decode_any W_6f6d8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj13Tg002mj1:Tg003Kj11Tg003ij32Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Mi#8R4P0P1g00Nhg00<BR5#0R6#3R7#:R8%35#0R5#3#1g00<gR932%05#1=289%07#1=289C7%06#1C6,52R634R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6dc : bv 32 := 0x00f6f693.
Lemma D_6f6dc : decode_any W_6f6dc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00OT#9R4P0P1g00PSg00<BR5#1R6#0#5%05R5#1R7#0#2g00<gR833R9P9%17#5%05#0#2;38C8%16#2C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6e0 : bv 32 := 0x02068063.
Lemma D_6f6e0 : decode_any W_6f6e0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Q?#9R4P0P1g00;Pg00<BR5#0R6#2#5R7%25#0#2R5#3g00<gR831g00=C=178%55%06R6#0#0#0#3;18C8%36C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6e4 : bv 32 := 0x04060863.
Lemma D_6f6e4 : decode_any W_6f6e4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00R>#9R4P0P1g00;Pg00<BR5#0R6#2R7#5R8%25#0R5#0#3g00<gR931g00=C=189%25#5%07#0#0#0#3;19C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6e8 : bv 32 := 0x00c50633.
Lemma D_6f6e8 : decode_any W_6f6e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00?kj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00S=#8R4P0P1g00AVg00<BR5#0R6#4R7#:R8%45#0#0#1g00<gR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6ec : bv 32 := 0x00050693.
Lemma D_6f6ec : decode_any W_6f6ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00T<#9R4P0P1g00AVg00<BR5#0R6#2R7#5R8%25#0R5#2#3g00<gR931%07#3=189%05#5g00=C;19C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6f0 : bv 32 := 0x00b68023.
Lemma D_6f6f0 : decode_any W_6f6f0 = Some (Store SZ1 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00Fdj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00U;#9R4P0P1g00EXg00<BR5#0R6#1R7#5R8%15#0R5#1#3g00<gR932%17#3=289%05#5g00=C;29C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6f4 : bv 32 := 0x00168693.
Lemma D_6f6f4 : decode_any W_6f6f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00V:#9R4P0P1g00AVg00<BR5#0R6#1#5%15#0R7#1#2g00<gR833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6f8 : bv 32 := 0xfec69ce3.
Lemma D_6f6f8 : decode_any W_6f6f8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00W9#9R4P0P1g00KLg00<BR5#1R6#0#5R7%05R5#1R8#0R9#2g00<gR:33%18#2=37:%59%05#0#0#0#0#0#0#0#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f6fc : bv 32 := 0x0380006f.
Lemma D_6f6fc : decode_any W_6f6fc = Some (Jal 0 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00X8j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Xd#9R4P0P1g00<BR5#0R6#1R7#5g00=Cg00<gR833%07#1#5%15#1#0#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f700 : bv 32 := 0x02060a63.
Lemma D_6f700 : decode_any W_6f700 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Yc#9R4P0P1g00;Pg00<BR5#0R6#2#5R7%25#0R5#0#3g00<gR831g00=C=178%25R5#5%05#0#3;18C8%06#3C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f704 : bv 32 := 0x00c50633.
Lemma D_6f704 : decode_any W_6f704 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00?kj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Zb#8R4P0P1g00AVg00<BR5#0R6#4R7#:R8%45#0#0#1g00<gR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f708 : bv 32 := 0x00859693.
Lemma D_6f708 : decode_any W_6f708 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00[aj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00\M#9R4P0P1g00]Lg00<BR5#1R6#0R7#5R8%05#1R5#0#2g00<gR933%07#2=389%55%16R6#1#2;39C8%26C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f70c : bv 32 := 0x00b6e5b3.
Lemma D_6f70c : decode_any W_6f70c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00^8#8R4P0P1g00Nhg00<BR5#2R6#0R7#:R8%07#1g00<gR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f710 : bv 32 := 0x01059693.
Lemma D_6f710 : decode_any W_6f710 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00[aj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00_7#9R4P0P1g00]Lg00<BR5#0R6#1R7#5R8%15#0R5#1#2g00<gR933%17#2=389%55%06R6#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f714 : bv 32 := 0x00b6e5b3.
Lemma D_6f714 : decode_any W_6f714 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00`6#8R4P0P1g00Nhg00<BR5#2R6#0R7#:R8%07#1g00<gR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f718 : bv 32 := 0x02059693.
Lemma D_6f718 : decode_any W_6f718 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00[aj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00a5#9R4P0P1g00]Lg00<BR5#0R6#1R7#5R8%15#0R5#1#2g00<gR933%17#2=389%55%06R6#0#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f71c : bv 32 := 0x00b6e5b3.
Lemma D_6f71c : decode_any W_6f71c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00b4#8R4P0P1g00Nhg00<BR5#2R6#0R7#:R8%07#1g00<gR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f720 : bv 32 := 0x00050693.
Lemma D_6f720 : decode_any W_6f720 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00c3#9R4P0P1g00AVg00<BR5#0R6#2R7#5R8%25#0R5#2#3g00<gR931%07#3=189%05#5g00=C;19C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f724 : bv 32 := 0x00b6b023.
Lemma D_6f724 : decode_any W_6f724 = Some (Store SZ8 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00Fdj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00d2#9R4P0P1g00e1g00<BR5#0R6#1R7#5R8%15#0R5#1#3g00<gR932%17#3=289%05#5g00=C;29C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f728 : bv 32 := 0x00b6b423.
Lemma D_6f728 : decode_any W_6f728 = Some (Store SZ8 13 11 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Fdj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00e]#9R4P0P1g00e1g00<BR5#0R6#1R7#5R8%15#0R5#1#2g00<gR933%17#2=389%05#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f72c : bv 32 := 0x01068693.
Lemma D_6f72c : decode_any W_6f72c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00f\#9R4P0P1g00AVg00<BR5#0R6#1#5%15#0R5#1#2g00<gR733R8P8%05#5%06R6#0#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f730 : bv 32 := 0xfec6eae3.
Lemma D_6f730 : decode_any W_6f730 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00g[#9R4P0P1g00hZg00<BR5#1R6#0#5R7%05R5#1R8#0R9#2g00<gR:33%18#2=37:%59%05#0#0#0#0#0#0#1#0#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6f734 : bv 32 := 0x00008067.
Lemma D_6f734 : decode_any W_6f734 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00L>j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00iL#9R4P0P1g00<BR5#0R6#5#3R7g00=CR8g00<gR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc08 : bv 32 := 0xff010113.
Lemma D_6fc08 : decode_any W_6fc08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00jK#9R4P0P1g00AVg00<BR5#1R6#0#5%26g00<gR733R8P8%05R5#1#1#5%05#0#0#0#0#0#1#1#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc0c : bv 32 := 0x00113423.
Lemma D_6fc0c : decode_any W_6fc0c = Some (Store SZ8 2 1 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00Fdj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00kJ#9R4P0P1g00e1g00<BR5#0R6#5#3R7%16g00<gR832%15=278%55#0#0#3%06R6#0#1;28C8%16C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc10 : bv 32 := 0x00058693.
Lemma D_6fc10 : decode_any W_6fc10 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00lI#9R4P0P1g00AVg00<BR5#0R6#1R7#5R8%15#0R5#1#3g00<gR932%17#3=289%05#5g00=C;29C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc14 : bv 32 := 0x00100713.
Lemma D_6fc14 : decode_any W_6fc14 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00mH#9R4P0P1g00AVg00<BR5#0R6#2#5R7%25R8#2#0#3g00<gR931g00=C=179%08#0#5%35;19C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc18 : bv 32 := 0x02871713.
Lemma D_6fc18 : decode_any W_6fc18 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00[aj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00nG#9R4P0P1g00]Lg00<BR5#0R6#1R7#5%15R5#1#0#2g00<gR833R9P9%05#5%07#0#0#2;38C8%06#2C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc1c : bv 32 := 0x00170593.
Lemma D_6fc1c : decode_any W_6fc1c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00oF#9R4P0P1g00AVg00<BR5#0R6#1R7#5R8%17#2g00<gR733%15R9#1#0#2=387%09#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc20 : bv 32 := 0x08b6f263.
Lemma D_6fc20 : decode_any W_6fc20 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g010E#9R4P0P1g011Dg00<BR5#0R6#1R7#5R8%15#0#1R5#2g00<gR933%17#2=389%55%06R6#0#0#1#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc24 : bv 32 := 0x00000593.
Lemma D_6fc24 : decode_any W_6fc24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0126#9R4P0P1g00AVg00<BR5#0R6#2R7#5R8%27#3g00<gR731g00=CR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc28 : bv 32 := 0x00d50733.
Lemma D_6fc28 : decode_any W_6fc28 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0135#8R4P0P1g00AVg00<BR5#0R6#2R7#:R8%25R5#2#0#1g00<gR933%07#1=389%05#2#1=389C7%06#1C6,52R634R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc2c : bv 32 := 0x00750793.
Lemma D_6fc2c : decode_any W_6fc2c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0144#9R4P0P1g00AVg00<BR5#0R6#1R7#5R8%15R5#1R9#1#2g00<gR:33%07#2=38:%05#0#5%29;3:C8%06#2C7,62R634R:P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc30 : bv 32 := 0xff87f793.
Lemma D_6fc30 : decode_any W_6fc30 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0153#9R4P0P1g00PSg00<BR5#1R6#0#5%05R5#0#0R7#2g00<gR833R9P9%15#1#5%07#0#0#0#0#1#1#1#2;38C8%16#2C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc34 : bv 32 := 0xff877613.
Lemma D_6fc34 : decode_any W_6fc34 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0162#9R4P0P1g00PSg00<BR5#1R6#0#5R7%05R5#1#1R8#2g00<gR933%05R5#1#2=379%58%05#0#0#0#0#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc38 : bv 32 := 0x02f57463.
Lemma D_6fc38 : decode_any W_6fc38 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0171#9R4P0P1g011Dg00<BR5#0R6#1R7#5R8%07R7#2g00<gR933%15R5#1#1#2=389%05#1#5%07#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc3c : bv 32 := 0x02068263.
Lemma D_6fc3c : decode_any W_6fc3c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0180#9R4P0P1g00;Pg00<BR5#0R6#1#5R7%15#0#1R5#3g00<gR832g00=C=278%55%06R6#1#0#0#3;28C8%36C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc40 : bv 32 := 0x00000593.
Lemma D_6fc40 : decode_any W_6fc40 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g018o#9R4P0P1g00AVg00<BR5#0R6#2R7#5R8%27#3g00<gR731g00=CR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc44 : bv 32 := 0x00150693.
Lemma D_6fc44 : decode_any W_6fc44 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g019n#9R4P0P1g00AVg00<BR5#0R6#3R7#5R8%35#0R9#3#1g00<gR:32%07#1=28:%09#5%15;2:C8%06#1C7,62R634R:P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc48 : bv 32 := 0x00068813.
Lemma D_6fc48 : decode_any W_6fc48 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01:m#9R4P0P1g00AVg00<BR5#0R6#2#5R7%06R6#0#0#3g00<gR831%25#0R5#2#3=178%05#5g00=C;18C8%36C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc4c : bv 32 := 0xfff6c683.
Lemma D_6fc4c : decode_any W_6fc4c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj12Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00Cmj59Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=1g009GR0g00:3R1'CR2#BR3g01;l#:R4P0P1g00EXg00FDg00<BR5#2R6#0#6%05R5#2R7#0#3g00<gR834R9P9%27#6%15#1#1#1#1#3;48D9%26#3C7,82R635R8P3P3%A3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_6fc50 : bv 32 := 0x00d5e5b3.
Lemma D_6fc50 : decode_any W_6fc50 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01<k#8R4P0P1g00Nhg00<BR5#2R6#0R7#:R8%07#1g00<gR733R9P9%05#2#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc54 : bv 32 := 0x00f87663.
Lemma D_6fc54 : decode_any W_6fc54 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01=j#9R4P0P1g011Dg00<BR5#0R6#1#5R7%06R6#0#0#2g00<gR833%15R5#1#1#2=378%05R5#1#5%05#2;38C8%26C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc58 : bv 32 := 0x00180693.
Lemma D_6fc58 : decode_any W_6fc58 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01>i#9R4P0P1g00AVg00<BR5#0R6#3#5R7%35#0R8#3#1g00<gR932%06R6#0#0#1=279%08#5%15;29C8%16C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc5c : bv 32 := 0xfee866e3.
Lemma D_6fc5c : decode_any W_6fc5c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01?h#9R4P0P1g00hZg00<BR5#1R6#0#5R7%16R6#1#1#2g00<gR833%05R5#0R9#1#2=378%15#0#5%09#0#0#0#0#1#0#0#1#1#2;38C8%26C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc60 : bv 32 := 0x00c7fa63.
Lemma D_6fc60 : decode_any W_6fc60 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01@g#9R4P0P1g011Dg00<BR5#0R6#1R7#5R8%15R5#1#1#2g00<gR933%05R5#0#2=389%15#5%07#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc64 : bv 32 := 0x0007b683.
Lemma D_6fc64 : decode_any W_6fc64 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00Cmj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Af#9R4P0P1g00e1g00?KR5g00<BR6#1R7#0#5R8%06R6#1R9#0#3g00<gR:32%06#0#3=28:%19#5g00=C;2:D8%17#3C7,62R734R:P3P3%:3P0g00=aP1g00>RC@,?2P4P7E<R7g00>kR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc68 : bv 32 := 0x00878793.
Lemma D_6fc68 : decode_any W_6fc68 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Be#9R4P0P1g00AVg00<BR5#0R6#1#5%15R5#1#1#2g00<gR733R8P8%05#0#5%06R6#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc6c : bv 32 := 0x00b6e5b3.
Lemma D_6fc6c : decode_any W_6fc6c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Cd#8R4P0P1g00Nhg00<BR5#2R6#0R7#:R8%07#1g00<gR733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc70 : bv 32 := 0xfec7eae3.
Lemma D_6fc70 : decode_any W_6fc70 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Dc#9R4P0P1g00hZg00<BR5#1R6#0#5R7%05R5#0#0R8#2g00<gR933%15R5#1#2=379%05#5%08#0#0#0#0#1#0#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc74 : bv 32 := 0x02a66063.
Lemma D_6fc74 : decode_any W_6fc74 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Eb#9R4P0P1g00hZg00<BR5#0R6#3R7#5R8%35#0R5#0#1g00<gR932%07#1=289%35#5%06R6#0#0#0#1;29C8%16C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc78 : bv 32 := 0x00e67e63.
Lemma D_6fc78 : decode_any W_6fc78 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Fa#9R4P0P1g011Dg00<BR5#0R6#1#5R7%15R5#0R8#0#2g00<gR933%15#0R5#2=379%18#5%05#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc7c : bv 32 := 0x40c70733.
Lemma D_6fc7c : decode_any W_6fc7c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00?kj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01G`#8R4P0P1g01H_g00<BR5#0R6#2#:R7%25R5#2#0#1g00<gR833R9P9%05#0#1=378C7%06#1C6,52R634R8P3P3%93P0g00=aP1g00>RC@,?2P4P6E;R6g00>kR4g00?KR2'<1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc80 : bv 32 := 0x00064503.
Lemma D_6fc80 : decode_any W_6fc80 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00Cmj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01IK#9R4P0P1g00EXg00FDg00<BR5#0R6#5R7#3R8%07#2g00<gR731%55#0#0R5#2=187%35g00=C;17D8%06#2C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc84 : bv 32 := 0xfff70713.
Lemma D_6fc84 : decode_any W_6fc84 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00BBj49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=2g009GR0g00:3R1'CR2#BR3g01JJ#:R4P0P1g00AVg00<BR5#1R6#0#6%05R5#0R7#1#3g00<gR834R9P9%15#1#6%07#2#2#2#2#3;48C9%16#3C7,82R635R8P3P3%A3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_6fc88 : bv 32 := 0x00a5e5b3.
Lemma D_6fc88 : decode_any W_6fc88 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj11Tg002Hj14Tg002mj1:Tg003Kj10Tg003ij32Tg00?kj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01KI#8R4P0P1g00Nhg00<B#1R5#4R6#:R7%46#0g00<gR832R9P9%16#0=278C7%15#0C6,52R533R8P3P3%93P0g00=aP1g00>RC@,?2P4P5E;R5g00>kR4g00?KR2'<1=85=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc8c : bv 32 := 0x00160613.
Lemma D_6fc8c : decode_any W_6fc8c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01LH#9R4P0P1g00AVg00<BR5#0R6#5#3%55#0#0R7#1g00<gR832R9P9%37%15;28C8%06#1C7,62R634R8P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc90 : bv 32 := 0xfe0718e3.
Lemma D_6fc90 : decode_any W_6fc90 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01MG#9R4P0P1g00KLg00<BR5#1R6#0#5R7%05R5#0R8#1#3g00<gR932g00=C=279%15#0#5%08#0#0#0#0#0#1#1#1#1#3;29C8%16#3C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc94 : bv 32 := 0x0015b513.
Lemma D_6fc94 : decode_any W_6fc94 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01NF#9R4P0P1g01OEg00<BR5#0R6#3R7#5R8%07#1g00<gR932%37#1=289%35#0#0#5%15;29C8%06#1C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc98 : bv 32 := 0x00813083.
Lemma D_6fc98 : decode_any W_6fc98 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00Cmj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01P1#9R4P0P1g00e1g00?KR5g00<BR6#0R7#5#3R8%16g00<gR932%17=289%56#0#0#3%07R7#0#1;29D8%17C7,62R734R9P3P3%:3P0g00=aP1g00>RC@,?2P4P7E<R7g00>kR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fc9c : bv 32 := 0x01010113.
Lemma D_6fc9c : decode_any W_6fc9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00BBj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Q0#9R4P0P1g00AVg00<BR5#0R6#5#3%16g00<gR732R8P8%55#0#0#3%06R6#0#0#1;27C8%16C7,62R634R7P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fca0 : bv 32 := 0x00008067.
Lemma D_6fca0 : decode_any W_6fca0 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00L>j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Qo#9R4P0P1g00<BR5#0R6#5#3R7g00=CR8g00<gR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=aP1g00>RC@,?2P4P6E<R6g00>kR4g00?KR2';1=96=442d3>o"). Qed.
