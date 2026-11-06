(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Sums2_code () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb04C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr08c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb08C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb0cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb10C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb14C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb18C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb1cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb20C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb24C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb28C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb2cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb30C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb34C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb38C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb3cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb44C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb48C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb4cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb50C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb54C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb58C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb5cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb60C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb68C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb6cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5instr04c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_6fb70C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0b4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0b8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0bcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0c0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0c4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0c8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0ccC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0d0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0d4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0d8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0dcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0e0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0e4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0e8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0ecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0f0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0f4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0f8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c0fcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c100C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c104C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c108C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c10cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c110C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c114C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c118C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c11cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c120C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c124C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c128C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c12cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c130C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c134C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c138C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c13cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c140C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c144C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c148C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c14cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c150C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c154C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c158C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c15cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c160C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c164C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c168C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c16cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c170C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c174C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c178C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c17cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c180C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c184C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c188C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c18cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c190C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c194C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c198C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c19cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1a0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1a4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1a8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1acC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1b0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1b4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1b8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1bcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1c0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1c4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1c8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1ccC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1d0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1d4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1d8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1dcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1e0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1e4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1e8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1ecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1f0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1f4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1f8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c1fcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c200C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c204C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c208C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02:Sums2_code7W_5c20cC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6fb04 : bv 32 := 0x06060663.
Lemma D_6fb04 : decode_any W_6fb04 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;Qg00<CR5#0R6#1#5R7%15#0R5#0#3g00<hR832g00=D=278%15R5#5%15#0#0#3;28C8%06#3C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb08 : bv 32 := 0x00000693.
Lemma D_6fb08 : decode_any W_6fb08 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@X#9R4P0P1g00AXg00<CR5#0R6#2#5R7%25#0R5#2#3g00<hR831g00=DR9=178%05#5?198C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb0c : bv 32 := 0x00d58733.
Lemma D_6fb0c : decode_any W_6fb0c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00C0#8R4P0P1g00AXg00<CR5#2R6#0R7#:R8%05R5#0#2#1g00<hR933%07#1=389%25#0#1=389C7%26#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb10 : bv 32 := 0x00074703.
Lemma D_6fb10 : decode_any W_6fb10 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00D\#9R4P0P1g00E\g00FHg00<CR5#0R6#1#5%15R5#1#0#3g00<hR732R8P8%05#0#5g00=D;27D8%06#3C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb14 : bv 32 := 0x00070c63.
Lemma D_6fb14 : decode_any W_6fb14 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Fh#9R4P0P1g00;Qg00<CR5#0R6#1#5R7%15R5#1#0#3g00<hR832g00=D=278%05R5#1#5%05#0#3;28C8%06#3C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb18 : bv 32 := 0x00d507b3.
Lemma D_6fb18 : decode_any W_6fb18 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Gh#8R4P0P1g00AXg00<CR5#2R6#0R7#:R8%05R5#0#0#1g00<hR933%27#1=389%25#0#1=389C7%26#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb1c : bv 32 := 0x00168693.
Lemma D_6fb1c : decode_any W_6fb1c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Hh#9R4P0P1g00AXg00<CR5#0R6#1#5%15#0R7#1#2g00<hR833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb20 : bv 32 := 0x00e78023.
Lemma D_6fb20 : decode_any W_6fb20 = Some (Store SZ1 15 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00JT#9R4P0P1g00E\g00<CR5#0R6#1#5R7%15R5#1R8#1#3g00<hR932%08#3=279%05#0#5g00=D;29C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb24 : bv 32 := 0xfed614e3.
Lemma D_6fb24 : decode_any W_6fb24 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00KT#9R4P0P1g00LTg00<CR5#1R6#0#5R7%05R5#1R8#1#2g00<hR933%08R8#2=379%58%05#0#0#0#0#0#1#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb28 : bv 32 := 0x00060693.
Lemma D_6fb28 : decode_any W_6fb28 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00MF#9R4P0P1g00AXg00<CR5#0R6#2#5R7%25#0R5#2#3g00<hR831%05R5#3=178%55g00=D;18C8%06#3C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb2c : bv 32 := 0x00d505b3.
Lemma D_6fb2c : decode_any W_6fb2c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00NF#8R4P0P1g00AXg00<CR5#0R6#2R7#:R8%27#1g00<hR933%07#1=389%25#0#2#1=389C7%06#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb30 : bv 32 := 0x40d6073b.
Lemma D_6fb30 : decode_any W_6fb30 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00OFj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00P2#8R4P0P1g00Q2g00<CR5#0R6#2#:R7%25R5#2#0#1g00<hR833%05R5#0#1=378%25#1=378C7%06#1C6,52R634R8P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb34 : bv 32 := 0x00b76733.
Lemma D_6fb34 : decode_any W_6fb34 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Q^#8R4P0P1g00R^g00<CR5#2R6#0R7#:R8%05#0#2#1g00<hR533R9P9%07#1=385C7%26#1C6,52R634R5P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=56=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb38 : bv 32 := 0x00f77713.
Lemma D_6fb38 : decode_any W_6fb38 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00SJ#9R4P0P1g00TJg00<CR5#0R6#1#5%15R5#1R7#0#2g00<hR833R9P9%05#0#5%17#2;38C8%06#2C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb3c : bv 32 := 0x00070e63.
Lemma D_6fb3c : decode_any W_6fb3c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00U6#9R4P0P1g00;Qg00<CR5#0R6#1#5R7%15R5#1#0R8#3g00<hR932g00=D=279%05#1#5%08#3;29C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb40 : bv 32 := 0x02d60863.
Lemma D_6fb40 : decode_any W_6fb40 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00V6#9R4P0P1g00;Qg00<CR5#0R6#3#5R7%35#0R5#0R8#1g00<hR932%35R5#1=279%55%08#0#1;29C8%06#1C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb44 : bv 32 := 0x00c50633.
Lemma D_6fb44 : decode_any W_6fb44 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00BDj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00W6#8R4P0P1g00AXg00<CR5#0R6#4R7#:R8%45#0#0#1g00<hR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb48 : bv 32 := 0x00058023.
Lemma D_6fb48 : decode_any W_6fb48 = Some (Store SZ1 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00X6#9R4P0P1g00E\g00<CR5#0R6#2R7#5R8%27#3g00<hR731g00=DR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb4c : bv 32 := 0x00158593.
Lemma D_6fb4c : decode_any W_6fb4c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Y6#9R4P0P1g00AXg00<CR5#0R6#1R7#5%17#2g00<hR733R8P8%15#0#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb50 : bv 32 := 0xfec59ce3.
Lemma D_6fb50 : decode_any W_6fb50 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Z6#9R4P0P1g00LTg00<CR5#1R6#0R7#5R8%07#2g00<hR733%05R5#1R9#1#2=387%09#5%05#0#0#0#0#0#0#0#1#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb54 : bv 32 := 0x01c0006f.
Lemma D_6fb54 : decode_any W_6fb54 = Some (Jal 0 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00[6j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00[b#9R4P0P1g00<CR5#0R6#1R7#5g00=Dg00<hR833%07#1#5%15#1#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb58 : bv 32 := 0x00d60c63.
Lemma D_6fb58 : decode_any W_6fb58 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00\b#9R4P0P1g00;Qg00<CR5#0R6#3#5R7%35#0R5#0R8#1g00<hR932%35R5#1=279%55%08#1;29C8%06#1C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb5c : bv 32 := 0x00c50633.
Lemma D_6fb5c : decode_any W_6fb5c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00BDj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00]b#8R4P0P1g00AXg00<CR5#0R6#4R7#:R8%45#0#0#1g00<hR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb60 : bv 32 := 0x0005b023.
Lemma D_6fb60 : decode_any W_6fb60 = Some (Store SZ8 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00^b#9R4P0P1g00_bg00<CR5#0R6#2R7#5R8%27#3g00<hR731g00=DR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb64 : bv 32 := 0x0005b423.
Lemma D_6fb64 : decode_any W_6fb64 = Some (Store SZ8 11 0 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00`N#9R4P0P1g00_bg00<CR5#0R6#2R7#5R8%27#3g00<hR731g00=D=187%25#0#0#5%06R6#0#3;17C8%36C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb68 : bv 32 := 0x01058593.
Lemma D_6fb68 : decode_any W_6fb68 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00aN#9R4P0P1g00AXg00<CR5#0R6#1R7#5%17#2g00<hR733R8P8%15#0#0#5%06R6#0#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb6c : bv 32 := 0xfec5eae3.
Lemma D_6fb6c : decode_any W_6fb6c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00bN#9R4P0P1g00cNg00<CR5#1R6#0R7#5R8%07#2g00<hR733%05R5#1R9#1#2=387%09#5%05#0#0#0#0#0#0#1#0#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_6fb70 : bv 32 := 0x00008067.
Lemma D_6fb70 : decode_any W_6fb70 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00d@j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00dl#9R4P0P1g00<CR5#0R6#5#3R7g00=DR8g00<hR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.



(* [comment removed for export] *)
Definition W_5c0b4 : bv 32 := 0x00200613.
Lemma D_5c0b4 : decode_any W_5c0b4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00el#9R4P0P1g00AXg00<CR5#0R6#5#3R7%55#0#0R5#2g00<hR831g00=D=178%35%26;18C8%06#2C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0b8 : bv 32 := 0x14c5ea63.
Lemma D_5c0b8 : decode_any W_5c0b8 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00fl#9R4P0P1g00cNg00<CR5#0R6#1R7#5R8%17#2g00<hR933%15#0R5#0#2=389%15#5%07#1#0#1#0#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0bc : bv 32 := 0x00100613.
Lemma D_5c0bc : decode_any W_5c0bc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00gl#9R4P0P1g00AXg00<CR5#0R6#5#3R7%55#0#0R8#2g00<hR931g00=D=179%38%25;19C8%06#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0c0 : bv 32 := 0x00100693.
Lemma D_5c0c0 : decode_any W_5c0c0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00hl#9R4P0P1g00AXg00<CR5#0R6#2#5R7%25#0R8#2#3g00<hR931g00=D=179%08#5%35;19C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0c4 : bv 32 := 0x00c0006f.
Lemma D_5c0c4 : decode_any W_5c0c4 = Some (Jal 0 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00[6j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00il#9R4P0P1g00<CR5#0R6#1R7#5g00=Dg00<hR833%07#1#5%15#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0c8 : bv 32 := 0x00160613.
Lemma D_5c0c8 : decode_any W_5c0c8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00jl#9R4P0P1g00AXg00<CR5#0R6#5#3%55#0#0R7#1g00<hR832R9P9%37%15;28C8%06#1C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0cc : bv 32 := 0x12b60c63.
Lemma D_5c0cc : decode_any W_5c0cc = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00kl#9R4P0P1g00;Qg00<CR5#1R6#0R7#5R8%05#1R5#1#2g00<hR933%07#2=389%05#5%16R6#0#0#0#1#1#1#2;39C8%26C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0d0 : bv 32 := 0x00461713.
Lemma D_5c0d0 : decode_any W_5c0d0 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00mX#9R4P0P1g00nXg00<CR5#0R6#2#5R7%25R5#2#0#3g00<hR831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0d4 : bv 32 := 0x00e50733.
Lemma D_5c0d4 : decode_any W_5c0d4 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00oD#8R4P0P1g00AXg00<CR5#0R6#2R7#:R8%25#2#0#1g00<hR533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0d8 : bv 32 := 0x00072703.
Lemma D_5c0d8 : decode_any W_5c0d8 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g010D#9R4P0P1g011Dg00?LR5g00<CR6#0R7#1#5%16R6#1#0#3g00<hR832R9P9%06#0#5g00=D;28D8%07#3C7,62R734R8P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0dc : bv 32 := 0x00060893.
Lemma D_5c0dc : decode_any W_5c0dc = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0120#9R4P0P1g00AXg00<CR5#0R6#2#5R7%06R6#0#2#3g00<hR831%25#0#0R5#3=178%55g00=D;18C8%36C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0e0 : bv 32 := 0xfff88793.
Lemma D_5c0e0 : decode_any W_5c0e0 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj12Tg002mj16Tg003Kj13Tg003ij34Tg00?lj49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#2#2p=0g009GR0g00:3R1'CR2#BR3g0130#:R4P0P1g00AXg00<CR5#1R6#2#6R7%25R5#0R8#3g00<hR934%16R6#1#2#3=479%15#1#6%08#0#0#0#3;49C9%36C7,82R635R9P3P3%A3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2'=1>96=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_5c0e4 : bv 32 := 0x0017d813.
Lemma D_5c0e4 : decode_any W_5c0e4 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0140#9R4P0P1g0150g00<CR5#0R6#1#5R7%06R6#0#0#2g00<hR833%15R9#1#1#2=378%09#5%25;38C8%26C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0e8 : bv 32 := 0x00481293.
Lemma D_5c0e8 : decode_any W_5c0e8 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g015\#9R4P0P1g00nXg00<CR5#0R6#5R7#3R8%27g00<hR731%06R6#0#0#2=187%55#0#3%26R6;17C8P6C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0ec : bv 32 := 0x005502b3.
Lemma D_5c0ec : decode_any W_5c0ec = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j15Tg001cj11Tg002Hj1@Tg002mj18Tg003Kj10Tg003ij32Tg00BDj46Tg0058j47Tg005Xj24Tg006:j33j19Tg006Tj4?Tg0072j2:Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g016\#5R4P0P1g00AXg00<C#1R5#@R6#8R7%06g00<hR832R9%16#0=278P9C6%15#0C7,42R533R9P3P3%93P0g00=bP1g00>SC?,:2P4P5E;R5g00>lR4g00?LR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0f0 : bv 32 := 0x0002a303.
Lemma D_5c0f0 : decode_any W_5c0f0 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g017\#9R4P0P1g011Dg00?LR5g00<CR6#0R7#5R8#3R9%56#0R6#2g00<hR:31%28=19:%06#3g00=D;1:D8%07#2C7,62R734R:P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0f4 : bv 32 := 0xfce37ae3.
Lemma D_5c0f4 : decode_any W_5c0f4 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g018\#9R4P0P1g019\g00<CR5#1R6#0#5R7%05R5#1R8#2g00<hR933%05R5#1#2=379%08#5%05#0#0#0#1#0#1#0#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0f8 : bv 32 := 0x0002b303.
Lemma D_5c0f8 : decode_any W_5c0f8 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01:N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#5R8#3R9%56#0R6#2g00<hR:31%28=19:%06#3g00=D;1:D8%07#2C7,62R734R:P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c0fc : bv 32 := 0x00489893.
Lemma D_5c0fc : decode_any W_5c0fc = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01;N#9R4P0P1g00nXg00<CR5#0R6#1#5%06R6#0#1#3g00<hR732R8P8%15#0#5%36R6;27C8P6C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c100 : bv 32 := 0x011508b3.
Lemma D_5c100 : decode_any W_5c100 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00BDj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01<N#8R4P0P1g00AXg00<C#0R5#4R6#:R7%05R5#0#4#1g00<hR832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00=bP1g00>SC@,?2P4P5E;R5g00>lR4g00?LR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c104 : bv 32 := 0x0048a383.
Lemma D_5c104 : decode_any W_5c104 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01=N#9R4P0P1g011Dg00?LR5g00<CR6#0R7#1#5R8%16R6#1#3g00<hR932%07R7#0#1#3=289%06#0#5%37R7;29D8P7C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c108 : bv 32 := 0x0068b023.
Lemma D_5c108 : decode_any W_5c108 = Some (Store SZ8 17 6 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01>N#9R4P0P1g00_bg00<CR5#0R6#2#5R7%06R6#0#2#3g00<hR831%25#0R5#3=178%05#5g00=D;18C8%36C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c10c : bv 32 := 0x0082b303.
Lemma D_5c10c : decode_any W_5c10c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01?N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#5R8#3R9%56#0R6#1g00<hR:32%18=29:%06#3%07R7#0#1;2:D8%17C7,62R734R:P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c110 : bv 32 := 0x0088be03.
Lemma D_5c110 : decode_any W_5c110 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01@N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#1#5R8%16R6#1#0#0#2g00<hR933%07R7#0R:#1#2=389%06#0#5%2:;39D8%27C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c114 : bv 32 := 0x0068b423.
Lemma D_5c114 : decode_any W_5c114 = Some (Store SZ8 17 6 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01AN#9R4P0P1g00_bg00<CR5#0R6#3#5R7%06R6#0R8#3#1g00<hR932%35#0R5#1=279%05#5%18;29C8%16C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c118 : bv 32 := 0x00e2a023.
Lemma D_5c118 : decode_any W_5c118 = Some (Store SZ4 5 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01BN#9R4P0P1g011Dg00<CR5#0R6#2R7#5R8%37g00<hR731%25R5#2#0#3=187%05#0#5g00=D;17C8%06#3C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c11c : bv 32 := 0x0072a223.
Lemma D_5c11c : decode_any W_5c11c = Some (Store SZ4 5 7 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01CN#9R4P0P1g011Dg00<CR5#0R6#2R7#5R8%37g00<hR731%25R5#2#3=187%05#0#5%06#3R6;17C8P6C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c120 : bv 32 := 0x01c2b423.
Lemma D_5c120 : decode_any W_5c120 = Some (Store SZ8 5 28 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01DN#9R4P0P1g00_bg00<CR5#0R6#3R7#5R8%17g00<hR732%35R5#3#0#0#1=287%05#0#5%06R6#0#1;27C8%16C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c124 : bv 32 := 0x00080893.
Lemma D_5c124 : decode_any W_5c124 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01EN#9R4P0P1g00AXg00<CR5#0R6#2#5R7%06R6#0R8#2#3g00<hR931%08#3=179%25#0#0#5g00=D;19C8%36C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c128 : bv 32 := 0xfaf6ece3.
Lemma D_5c128 : decode_any W_5c128 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01FN#9R4P0P1g00cNg00<CR5#1R6#0#5R7%05R5#1#0R8#2g00<hR933%05#0R5#2=379%58%05#0#1#0#0#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c12c : bv 32 := 0xf9dff06f.
Lemma D_5c12c : decode_any W_5c12c = Some (Jal 0 2097052, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj12Tg002mj14Tg003ij36Tg003Kj13Tg00[6j29Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#2#2p=0g009GR0g00:3R1'CR2#BR3g01GN#:R4P0P1g00<CR5#1R6#2R7#4g00=Dg00<hR836%17#2#4%25#0#0#0#0#0#0#1#1#2#0#1#1#3;68'9%16#3C7,82R635R8P3P3%A3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_5c130 : bv 32 := 0x00000613.
Lemma D_5c130 : decode_any W_5c130 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01HN#9R4P0P1g00AXg00<CR5#0R6#5#2R7%55#0#0R5#3g00<hR831g00=DR9=178%25?198C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c134 : bv 32 := 0x00459693.
Lemma D_5c134 : decode_any W_5c134 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01IN#9R4P0P1g00nXg00<CR5#1R6#0R7#5R8%05#1R5#0#3g00<hR932%07#3=289%55%16#3R6;29C8P6C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c138 : bv 32 := 0x00d506b3.
Lemma D_5c138 : decode_any W_5c138 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01JN#8R4P0P1g00AXg00<CR5#0R6#2R7#:R8%25#0#2#1g00<hR533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c13c : bv 32 := 0x0006b703.
Lemma D_5c13c : decode_any W_5c13c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01KN#9R4P0P1g00_bg00?LR5g00<CR6#0R7#1#5R8%16R6#1#0#3g00<hR932%06R6#1#3=289%06#5g00=D;29D8%07#3C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c140 : bv 32 := 0x0086b783.
Lemma D_5c140 : decode_any W_5c140 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01LN#9R4P0P1g00_bg00?LR5g00<CR6#1R7#0#5R8%06R6#0#0#2g00<hR933%16R6#0#2=389%16#5%17R7#1#2;39D8%27C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c144 : bv 32 := 0x00053803.
Lemma D_5c144 : decode_any W_5c144 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01MN#9R4P0P1g00_bg00?LR5g00<CR6#0R7#5R8#3R9%07R7#0#0#2g00<hR:31%08#2=19:%56#0#0#3g00=D;1:D8%27C7,62R734R:P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c148 : bv 32 := 0x00853883.
Lemma D_5c148 : decode_any W_5c148 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01NN#9R4P0P1g00_bg00?LR5g00<CR6#0R7#3R8#5R9%07R7#0R:#3#1g00<hR;32%08#1=29;%36#0#0#5%1:;2;D8%17C7,62R734R;P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=;7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c14c : bv 32 := 0x00e53023.
Lemma D_5c14c : decode_any W_5c14c = Some (Store SZ8 10 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01ON#9R4P0P1g00_bg00<CR5#0R6#2R7#5R8%07#3g00<hR731%25R5#2#0#3=187%05#0#5g00=D;17C8%06#3C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c150 : bv 32 := 0x00f53423.
Lemma D_5c150 : decode_any W_5c150 = Some (Store SZ8 10 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01PN#9R4P0P1g00_bg00<CR5#0R6#1R7#5R8%07#2g00<hR733%15R5#1#1#2=387%05#0#5%06R6#0#2;37C8%26C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c154 : bv 32 := 0x0106b023.
Lemma D_5c154 : decode_any W_5c154 = Some (Store SZ8 13 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01QN#9R4P0P1g00_bg00<CR5#0R6#2#5R7%25#0R5#2#3g00<hR831%06R6#0#0#3=178%05#5g00=D;18C8%36C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c158 : bv 32 := 0x0116b423.
Lemma D_5c158 : decode_any W_5c158 = Some (Store SZ8 13 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01RN#9R4P0P1g00_bg00<CR5#0R6#1#5R7%15#0R5#1#2g00<hR833%06R6#0R9#1#2=378%05#5%29;38C8%26C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c15c : bv 32 := 0x00000693.
Lemma D_5c15c : decode_any W_5c15c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01SN#9R4P0P1g00AXg00<CR5#0R6#2#5R7%25#0R5#2#3g00<hR831g00=DR9=178%05#5?198C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c160 : bv 32 := 0x00161793.
Lemma D_5c160 : decode_any W_5c160 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01TN#9R4P0P1g00nXg00<CR5#1R6#0#5R7%05R8#0#0#2g00<hR933%18R8#1#2=379%58%25;39C8%16#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c164 : bv 32 := 0x00178813.
Lemma D_5c164 : decode_any W_5c164 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01UN#9R4P0P1g00AXg00<CR5#0R6#1#5R7%06R6#0#0#2g00<hR833%15R9#1#1#2=378%09#0#5%25;38C8%26C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c168 : bv 32 := 0x00461713.
Lemma D_5c168 : decode_any W_5c168 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01VN#9R4P0P1g00nXg00<CR5#0R6#2#5R7%25R5#2#0#3g00<hR831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c16c : bv 32 := 0x00b86a63.
Lemma D_5c16c : decode_any W_5c16c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01WN#9R4P0P1g00cNg00<CR5#0R6#1R7#5R8%06R6#0#0#2g00<hR933%17#2=389%15#0#1#5%07#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c170 : bv 32 := 0x00278793.
Lemma D_5c170 : decode_any W_5c170 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01XN#9R4P0P1g00AXg00<CR5#1R6#0#5%05R5#0#0#2g00<hR733R8P8%15#1#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c174 : bv 32 := 0x02b7ea63.
Lemma D_5c174 : decode_any W_5c174 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01YN#9R4P0P1g00cNg00<CR5#1R6#0R7#5R8%05R5#0#0#2g00<hR933%07#2=389%15#0R5#5%15#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c178 : bv 32 := 0x04c69c63.
Lemma D_5c178 : decode_any W_5c178 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01ZN#9R4P0P1g00LTg00<CR5#0R6#1R7#5R8%15#0R5#1R9#2g00<hR:33%05#2=38:%59%17#0#0#0#2;3:C8%06#2C7,62R634R:P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c17c : bv 32 := 0x0880006f.
Lemma D_5c17c : decode_any W_5c17c = Some (Jal 0 136, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00[6j28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01[N#9R4P0P1g00<C#0R5#1R6#5g00=Dg00<hR733%06#1#5%05R5#0#1#0#0#0#2;37'8%25C7,62R534R7P3P3%:3P0g00=bP1g00>SC@,?2P4P5E<R5g00>lR4g00?LR2';1=75=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c180 : bv 32 := 0x00e506b3.
Lemma D_5c180 : decode_any W_5c180 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01\N#8R4P0P1g00AXg00<CR5#0R6#2R7#:R8%25R5#0#2#1g00<hR933%07#1=389%25#0#1=389C7%06#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c184 : bv 32 := 0x00481893.
Lemma D_5c184 : decode_any W_5c184 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01]N#9R4P0P1g00nXg00<CR5#0R6#2#5R7%06R6#0R8#2#3g00<hR931%08#3=179%25#0#5%36R6;19C8P6C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c188 : bv 32 := 0x011508b3.
Lemma D_5c188 : decode_any W_5c188 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00BDj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01^N#8R4P0P1g00AXg00<C#0R5#4R6#:R7%05R5#0#4#1g00<hR832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00=bP1g00>SC@,?2P4P5E;R5g00>lR4g00?LR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c18c : bv 32 := 0x0006a683.
Lemma D_5c18c : decode_any W_5c18c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01_N#9R4P0P1g011Dg00?LR5g00<CR6#0R7#1#5%16#0R6#1#3g00<hR832R9P9%06#5g00=D;28D8%07#3C7,62R734R8P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c190 : bv 32 := 0x0008a883.
Lemma D_5c190 : decode_any W_5c190 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01`N#9R4P0P1g011Dg00?LR5g00<CR6#0R7#1#5%07R7#0#1#3g00<hR832R9P9%16#0#0#5g00=D;28D8%37C7,62R734R8P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c194 : bv 32 := 0x0116e463.
Lemma D_5c194 : decode_any W_5c194 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01aN#9R4P0P1g00cNg00<CR5#1R6#0#5R7%05#1#0R5#2g00<hR833%16R6#1R9#0#2=378%55%29;38C8%26C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c198 : bv 32 := 0x00060813.
Lemma D_5c198 : decode_any W_5c198 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01bN#9R4P0P1g00AXg00<CR5#0R6#5#3R7%06R6#0#0#2g00<hR831%55#0#0R5#2=178%35g00=D;18C8%26C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c19c : bv 32 := 0x00080693.
Lemma D_5c19c : decode_any W_5c19c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01cN#9R4P0P1g00AXg00<CR5#0R6#2#5R7%25#0R5#2#3g00<hR831%06R6#0#0#3=178%05#5g00=D;18C8%36C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1a0 : bv 32 := 0x00278793.
Lemma D_5c1a0 : decode_any W_5c1a0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01dN#9R4P0P1g00AXg00<CR5#1R6#0#5%05R5#0#0#2g00<hR733R8P8%15#1#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1a4 : bv 32 := 0xfcb7fae3.
Lemma D_5c1a4 : decode_any W_5c1a4 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01eN#9R4P0P1g019\g00<CR5#1R6#0R7#5R8%05R5#0#0R9#2g00<hR:33%07#2=38:%15#0#5%09#0#0#1#0#1#0#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1a8 : bv 32 := 0x00469813.
Lemma D_5c1a8 : decode_any W_5c1a8 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01fN#9R4P0P1g00nXg00<CR5#0R6#2#5R7%06R6#0#0#3g00<hR831%25#0R5#2#3=178%55%36R6;18C8P6C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1ac : bv 32 := 0x00479893.
Lemma D_5c1ac : decode_any W_5c1ac = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01gN#9R4P0P1g00nXg00<CR5#1R6#0#5R7%16R6#1#0#3g00<hR832%05R5#0#0#3=278%15#5%36R6;28C8P6C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1b0 : bv 32 := 0x01050833.
Lemma D_5c1b0 : decode_any W_5c1b0 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j15Tg001cj10Tg002Hj1@Tg002mj18Tg003Kj11Tg003ij32Tg00BDj46Tg0058j47Tg005Xj24Tg006:j33j19Tg006Tj4?Tg0072j2:Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01hN#5R4P0P1g00AXg00<C#0R5#@R6#8R7%05R5#0#0#1g00<hR832R9%06#1=278P9C6%15C7,42R533R9P3P3%93P0g00=bP1g00>SC?,:2P4P5E;R5g00>lR4g00?LR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1b4 : bv 32 := 0x011508b3.
Lemma D_5c1b4 : decode_any W_5c1b4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00BDj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01iN#8R4P0P1g00AXg00<C#0R5#4R6#:R7%05R5#0#4#1g00<hR832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00=bP1g00>SC@,?2P4P5E;R5g00>lR4g00?LR2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1b8 : bv 32 := 0x00082803.
Lemma D_5c1b8 : decode_any W_5c1b8 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003Kj13Tg003ij31Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01jN#9R4P0P1g011Dg00?LR5g00<CR6#0R7#5#2%07R7#0#0#3g00<hR831R9P9%56#0#0#2g00=D;18D8%37C7,62R734R8P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1bc : bv 32 := 0x0008a883.
Lemma D_5c1bc : decode_any W_5c1bc = Some (Load SZ4 true 17 17 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01kN#9R4P0P1g011Dg00?LR5g00<CR6#0R7#1#5%07R7#0#1#3g00<hR832R9P9%16#0#0#5g00=D;28D8%37C7,62R734R8P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1c0 : bv 32 := 0x01186463.
Lemma D_5c1c0 : decode_any W_5c1c0 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01lN#9R4P0P1g00cNg00<CR5#0R6#1#5R7%06R6#0R8#0#2g00<hR933%18#2=379%15#0#1#5%28;39C8%26C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1c4 : bv 32 := 0x00068793.
Lemma D_5c1c4 : decode_any W_5c1c4 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01mN#9R4P0P1g00AXg00<CR5#1R6#0#5R7%05R5#0#0#3g00<hR832%15R5#0#3=278%15#5g00=D;28C8%16#3C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1c8 : bv 32 := 0x00078693.
Lemma D_5c1c8 : decode_any W_5c1c8 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01nN#9R4P0P1g00AXg00<CR5#1R6#0#5R7%05R5#1R8#0#3g00<hR932%05#0#3=279%18#5g00=D;29C8%16#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1cc : bv 32 := 0x02c78c63.
Lemma D_5c1cc : decode_any W_5c1cc = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01oN#9R4P0P1g00;Qg00<CR5#0R6#1#5R7%15R5#1R8#1#2g00<hR933%05R5#0#2=379%15#5%08#0#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1d0 : bv 32 := 0x00469613.
Lemma D_5c1d0 : decode_any W_5c1d0 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00llj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g020N#9R4P0P1g00nXg00<CR5#0R6#2#5R7%25#0R5#0#3g00<hR831%25#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1d4 : bv 32 := 0x00c50633.
Lemma D_5c1d4 : decode_any W_5c1d4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00BDj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g021N#8R4P0P1g00AXg00<CR5#0R6#4R7#:R8%45#0#0#1g00<hR532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1d8 : bv 32 := 0x00063783.
Lemma D_5c1d8 : decode_any W_5c1d8 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g022N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#1#5R8%16R6#1#1#3g00<hR932%06#0R6#3=289%56g00=D;29D8%07#3C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1dc : bv 32 := 0x00e50733.
Lemma D_5c1dc : decode_any W_5c1dc = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00BDj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g023N#8R4P0P1g00AXg00<CR5#0R6#2R7#:R8%25#2#0#1g00<hR533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00=bP1g00>SC@,?2P4P6E;R6g00>lR4g00?LR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1e0 : bv 32 := 0x00073803.
Lemma D_5c1e0 : decode_any W_5c1e0 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g024N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#2#5R8%07R7#0#0#3g00<hR931%26R6#2#0#3=189%06#0#5g00=D;19D8%37C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1e4 : bv 32 := 0x00873883.
Lemma D_5c1e4 : decode_any W_5c1e4 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g025N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#1#5R8%07R7#0R9#1#2g00<hR:33%16R6#1#0#2=38:%06#0#5%29;3:D8%27C7,62R734R:P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1e8 : bv 32 := 0x00f73023.
Lemma D_5c1e8 : decode_any W_5c1e8 = Some (Store SZ8 14 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g026N#9R4P0P1g00_bg00<CR5#0R6#1#5R7%15R5#1R8#0#3g00<hR932%18#3=279%05#0#5g00=D;29C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1ec : bv 32 := 0x00863783.
Lemma D_5c1ec : decode_any W_5c1ec = Some (Load SZ8 true 15 12 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00D0j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g027N#9R4P0P1g00_bg00?LR5g00<CR6#0R7#1#5R8%16R6#1#1#2g00<hR933%06#0R6#2=389%56%07R7#0#2;39D8%27C7,62R734R9P3P3%:3P0g00=bP1g00>SC@,?2P4P7E<R7g00>lR4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1f0 : bv 32 := 0x00f73423.
Lemma D_5c1f0 : decode_any W_5c1f0 = Some (Store SZ8 14 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g028N#9R4P0P1g00_bg00<CR5#0R6#1#5R7%15R5#1R8#0#2g00<hR933%18#2=379%05#0#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1f4 : bv 32 := 0x01063023.
Lemma D_5c1f4 : decode_any W_5c1f4 = Some (Store SZ8 12 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g029N#9R4P0P1g00_bg00<CR5#0R6#5#3R7%55#0#0R5#2g00<hR831%06R6#0#0#2=178%35g00=D;18C8%26C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1f8 : bv 32 := 0x01163423.
Lemma D_5c1f8 : decode_any W_5c1f8 = Some (Store SZ8 12 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00Ihj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02:N#9R4P0P1g00_bg00<CR5#0R6#3#5R7%35#0#0R5#1g00<hR832%06R6#0R9#3#1=278%55%19;28C8%16C7,62R634R8P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c1fc : bv 32 := 0x00068613.
Lemma D_5c1fc : decode_any W_5c1fc = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00?lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02;N#9R4P0P1g00AXg00<CR5#0R6#2#5R7%25#0R5#0R8#3g00<hR931%25#3=179%58g00=D;19C8%06#3C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c200 : bv 32 := 0xf6b6e0e3.
Lemma D_5c200 : decode_any W_5c200 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02<N#9R4P0P1g00cNg00<CR5#1R6#0R7#5R8%05R5#1#0R9#2g00<hR:33%07#2=38:%59%05#0#0#1#0#0#1#1#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c204 : bv 32 := 0xfff58593.
Lemma D_5c204 : decode_any W_5c204 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj12Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00?lj49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=1g009GR0g00:3R1'CR2#BR3g02=N#:R4P0P1g00AXg00<CR5#2R6#0R7#6%07#3g00<hR734R8P8%05R5#2#2#6%15#1#1#1#1#3;47C9%26#3C7,82R635R7P3P3%A3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2'=1>76=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_5c208 : bv 32 := 0xf20594e3.
Lemma D_5c208 : decode_any W_5c208 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02>N#9R4P0P1g00LTg00<CR5#0R6#1R7#5R8%17#3g00<hR732g00=D=287%15R5#0#1#5%15#1#1#0#0#1#0#1#0#0#0#3;27C8%06#3C7,62R634R7P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_5c20c : bv 32 := 0x00008067.
Lemma D_5c20c : decode_any W_5c20c = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_code ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00d@j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02?N#9R4P0P1g00<CR5#0R6#5#3R7g00=DR8g00<hR931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=bP1g00>SC@,?2P4P6E<R6g00>lR4g00?LR2';1=96=442d3>o"). Qed.
