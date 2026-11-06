(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Sums_codeK () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_10375cC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103760C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr08c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103764C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103768C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr5instr07c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_10376cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103770C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103774C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103778C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5instr04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_10377cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037d8C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037dcC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037e0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037e4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037e8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037ecC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037f0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037f4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037f8C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_1037fcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103800C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103804C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103808C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_10380cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103810C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103814C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103818C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_10381cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103820C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103824C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103828C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_10382cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103830C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103834C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e3cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e40C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e44C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e48C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e4cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e50C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e54C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e58C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e5cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e60C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e64C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e68C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e6cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e70C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e74C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e78C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e7cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e80C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e84C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e88C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e8cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e90C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e94C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e98C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103e9cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ea0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ea4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ea8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103eacC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103eb0C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103eb4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103eb8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ebcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ec0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ec4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ec8C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop05c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103eccC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ed0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:Sums_codeK8W_103ed4C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_10375c : bv 32 := 0x02060063.
Lemma D_10375c : decode_any W_10375c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;_g00<QR5#0R6#2#5R7%25#0R5#0#3g00=6R831g00=R=178%25#5%06R6#0#0#0#3;18C8%36C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103760 : bv 32 := 0x00c50633.
Lemma D_103760 : decode_any W_103760 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00@:j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@f#8R4P0P1g00B4g00<QR5#0R6#4R7#:R8%45#0#0#1g00=6R532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103764 : bv 32 := 0x00050693.
Lemma D_103764 : decode_any W_103764 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00CL#9R4P0P1g00B4g00<QR5#0R6#2R7#5R8%25#0R5#2#3g00=6R931%07#3=189%05#5g00=R;19C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103768 : bv 32 := 0x0005c703.
Lemma D_103768 : decode_any W_103768 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00DZj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00EF#9R4P0P1g00FTg00G@g00<QR5#0R6#1R7#5R8%15R5#1#0#3g00=6R932%17#3=289%05#0#5g00=R;29D8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_10376c : bv 32 := 0x00e68023.
Lemma D_10376c : decode_any W_10376c = Some (Store SZ1 13 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00G`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00HL#9R4P0P1g00FTg00<QR5#0R6#1#5R7%15R5#0R8#1#3g00=6R932%15#0#3=279%08#5g00=R;29C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103770 : bv 32 := 0x00168693.
Lemma D_103770 : decode_any W_103770 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00IZ#9R4P0P1g00B4g00<QR5#0R6#1#5%15#0R7#1#2g00=6R833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103774 : bv 32 := 0x00158593.
Lemma D_103774 : decode_any W_103774 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Jh#9R4P0P1g00B4g00<QR5#0R6#1R7#5%17#2g00=6R733R8P8%15#0#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103778 : bv 32 := 0xfec698e3.
Lemma D_103778 : decode_any W_103778 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00L6#9R4P0P1g00MDg00<QR5#1R6#0#5R7%05R5#1R8#0R9#2g00=6R:33%18#2=37:%59%05#0#0#0#0#0#0#1#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_10377c : bv 32 := 0x00008067.
Lemma D_10377c : decode_any W_10377c = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00N6j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Nb#9R4P0P1g00<QR5#0R6#5#3R7g00=RR8g00=6R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037d8 : bv 32 := 0x00a666b3.
Lemma D_1037d8 : decode_any W_1037d8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj13Tg002mj1:Tg003Kj11Tg003ij32Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00P0#8R4P0P1g00Q>g00<QR5#0R6#3R7#:R8%35#0R5#3#1g00=6R932%05#1=289%07#1=289C7%06#1C6,52R634R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037dc : bv 32 := 0x00f6f693.
Lemma D_1037dc : decode_any W_1037dc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Qj#9R4P0P1g00S8g00<QR5#1R6#0#5%05R5#1R7#0#2g00=6R833R9P9%17#5%05#0#2;38C8%16#2C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037e0 : bv 32 := 0x02068063.
Lemma D_1037e0 : decode_any W_1037e0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Sd#9R4P0P1g00;_g00<QR5#0R6#2#5R7%25#0#2R5#3g00=6R831g00=R=178%55%06R6#0#0#0#3;18C8%36C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037e4 : bv 32 := 0x04060863.
Lemma D_1037e4 : decode_any W_1037e4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00U2#9R4P0P1g00;_g00<QR5#0R6#2R7#5R8%25#0R5#0#3g00=6R931g00=R=189%25#5%07#0#0#0#3;19C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037e8 : bv 32 := 0x00c50633.
Lemma D_1037e8 : decode_any W_1037e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00@:j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00V@#8R4P0P1g00B4g00<QR5#0R6#4R7#:R8%45#0#0#1g00=6R532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037ec : bv 32 := 0x00050693.
Lemma D_1037ec : decode_any W_1037ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00WN#9R4P0P1g00B4g00<QR5#0R6#2R7#5R8%25#0R5#2#3g00=6R931%07#3=189%05#5g00=R;19C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037f0 : bv 32 := 0x00b68023.
Lemma D_1037f0 : decode_any W_1037f0 = Some (Store SZ1 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00G`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00X\#9R4P0P1g00FTg00<QR5#0R6#1R7#5R8%15#0R5#1#3g00=6R932%17#3=289%05#5g00=R;29C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037f4 : bv 32 := 0x00168693.
Lemma D_1037f4 : decode_any W_1037f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Yj#9R4P0P1g00B4g00<QR5#0R6#1#5%15#0R7#1#2g00=6R833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037f8 : bv 32 := 0xfec69ce3.
Lemma D_1037f8 : decode_any W_1037f8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00[8#9R4P0P1g00MDg00<QR5#1R6#0#5R7%05R5#1R8#0R9#2g00=6R:33%18#2=37:%59%05#0#0#0#0#0#0#0#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_1037fc : bv 32 := 0x0380006f.
Lemma D_1037fc : decode_any W_1037fc = Some (Jal 0 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00\Fj28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00]2#9R4P0P1g00<QR5#0R6#1R7#5g00=Rg00=6R833%07#1#5%15#1#0#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103800 : bv 32 := 0x02060a63.
Lemma D_103800 : decode_any W_103800 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00^@#9R4P0P1g00;_g00<QR5#0R6#2#5R7%25#0R5#0#3g00=6R831g00=R=178%25R5#5%05#0#3;18C8%06#3C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103804 : bv 32 := 0x00c50633.
Lemma D_103804 : decode_any W_103804 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00@:j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00_N#8R4P0P1g00B4g00<QR5#0R6#4R7#:R8%45#0#0#1g00=6R532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103808 : bv 32 := 0x00859693.
Lemma D_103808 : decode_any W_103808 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00`\j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00aH#9R4P0P1g00bVg00<QR5#1R6#0R7#5R8%05#1R5#0#2g00=6R933%07#2=389%55%16R6#1#2;39C8%26C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_10380c : bv 32 := 0x00b6e5b3.
Lemma D_10380c : decode_any W_10380c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00cB#8R4P0P1g00Q>g00<QR5#2R6#0R7#:R8%07#1g00=6R733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103810 : bv 32 := 0x01059693.
Lemma D_103810 : decode_any W_103810 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00`\j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00dP#9R4P0P1g00bVg00<QR5#0R6#1R7#5R8%15#0R5#1#2g00=6R933%17#2=389%55%06R6#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103814 : bv 32 := 0x00b6e5b3.
Lemma D_103814 : decode_any W_103814 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00e^#8R4P0P1g00Q>g00<QR5#2R6#0R7#:R8%07#1g00=6R733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103818 : bv 32 := 0x02059693.
Lemma D_103818 : decode_any W_103818 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00`\j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00fl#9R4P0P1g00bVg00<QR5#0R6#1R7#5R8%15#0R5#1#2g00=6R933%17#2=389%55%06R6#0#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_10381c : bv 32 := 0x00b6e5b3.
Lemma D_10381c : decode_any W_10381c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00h:#8R4P0P1g00Q>g00<QR5#2R6#0R7#:R8%07#1g00=6R733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103820 : bv 32 := 0x00050693.
Lemma D_103820 : decode_any W_103820 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00iH#9R4P0P1g00B4g00<QR5#0R6#2R7#5R8%25#0R5#2#3g00=6R931%07#3=189%05#5g00=R;19C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103824 : bv 32 := 0x00b6b023.
Lemma D_103824 : decode_any W_103824 = Some (Store SZ8 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00G`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00jV#9R4P0P1g00kdg00<QR5#0R6#1R7#5R8%15#0R5#1#3g00=6R932%17#3=289%05#5g00=R;29C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103828 : bv 32 := 0x00b6b423.
Lemma D_103828 : decode_any W_103828 = Some (Store SZ8 13 11 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00G`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00lP#9R4P0P1g00kdg00<QR5#0R6#1R7#5R8%15#0R5#1#2g00=6R933%17#2=389%05#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_10382c : bv 32 := 0x01068693.
Lemma D_10382c : decode_any W_10382c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00m^#9R4P0P1g00B4g00<QR5#0R6#1#5%15#0R5#1#2g00=6R733R8P8%05#5%06R6#0#0#2;37C8%26C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103830 : bv 32 := 0xfec6eae3.
Lemma D_103830 : decode_any W_103830 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00nl#9R4P0P1g010:g00<QR5#1R6#0#5R7%05R5#1R8#0R9#2g00=6R:33%18#2=37:%59%05#0#0#0#0#0#0#1#0#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103834 : bv 32 := 0x00008067.
Lemma D_103834 : decode_any W_103834 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00N6j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g010l#9R4P0P1g00<QR5#0R6#5#3R7g00=RR8g00=6R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e3c : bv 32 := 0xff010113.
Lemma D_103e3c : decode_any W_103e3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g012:#9R4P0P1g00B4g00<QR5#1R6#0#5%26g00=6R733R8P8%05R5#1#1#5%05#0#0#0#0#0#1#1#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e40 : bv 32 := 0x00113423.
Lemma D_103e40 : decode_any W_103e40 = Some (Store SZ8 2 1 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00G`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g013H#9R4P0P1g00kdg00<QR5#0R6#5#3R7%16g00=6R832%15=278%55#0#0#3%06R6#0#1;28C8%16C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e44 : bv 32 := 0x00058693.
Lemma D_103e44 : decode_any W_103e44 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g014V#9R4P0P1g00B4g00<QR5#0R6#1R7#5R8%15#0R5#1#3g00=6R932%17#3=289%05#5g00=R;29C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e48 : bv 32 := 0x00100713.
Lemma D_103e48 : decode_any W_103e48 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g015d#9R4P0P1g00B4g00<QR5#0R6#2#5R7%25R8#2#0#3g00=6R931g00=R=179%08#0#5%35;19C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e4c : bv 32 := 0x02871713.
Lemma D_103e4c : decode_any W_103e4c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00`\j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0172#9R4P0P1g00bVg00<QR5#0R6#1R7#5%15R5#1#0#2g00=6R833R9P9%05#5%07#0#0#2;38C8%06#2C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e50 : bv 32 := 0x00170593.
Lemma D_103e50 : decode_any W_103e50 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g018@#9R4P0P1g00B4g00<QR5#0R6#1R7#5R8%17#2g00=6R733%15R9#1#0#2=387%09#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e54 : bv 32 := 0x08b6f263.
Lemma D_103e54 : decode_any W_103e54 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g019N#9R4P0P1g01:\g00<QR5#0R6#1R7#5R8%15#0#1R5#2g00=6R933%17#2=389%55%06R6#0#0#1#0#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e58 : bv 32 := 0x00000593.
Lemma D_103e58 : decode_any W_103e58 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01;N#9R4P0P1g00B4g00<QR5#0R6#2R7#5R8%27#3g00=6R731g00=RR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e5c : bv 32 := 0x00d50733.
Lemma D_103e5c : decode_any W_103e5c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01<\#8R4P0P1g00B4g00<QR5#0R6#2R7#:R8%25R5#2#0#1g00=6R933%07#1=389%05#2#1=389C7%06#1C6,52R634R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e60 : bv 32 := 0x00750793.
Lemma D_103e60 : decode_any W_103e60 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01=j#9R4P0P1g00B4g00<QR5#0R6#1R7#5R8%15R5#1R9#1#2g00=6R:33%07#2=38:%05#0#5%29;3:C8%06#2C7,62R634R:P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e64 : bv 32 := 0xff87f793.
Lemma D_103e64 : decode_any W_103e64 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01?8#9R4P0P1g00S8g00<QR5#1R6#0#5%05R5#0#0R7#2g00=6R833R9P9%15#1#5%07#0#0#0#0#1#1#1#2;38C8%16#2C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e68 : bv 32 := 0xff877613.
Lemma D_103e68 : decode_any W_103e68 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01@F#9R4P0P1g00S8g00<QR5#1R6#0#5R7%05R5#1#1R8#2g00=6R933%05R5#1#2=379%58%05#0#0#0#0#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e6c : bv 32 := 0x02f57463.
Lemma D_103e6c : decode_any W_103e6c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01AT#9R4P0P1g01:\g00<QR5#0R6#1R7#5R8%07R7#2g00=6R933%15R5#1#1#2=389%05#1#5%07#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e70 : bv 32 := 0x02068263.
Lemma D_103e70 : decode_any W_103e70 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Bb#9R4P0P1g00;_g00<QR5#0R6#1#5R7%15#0#1R5#3g00=6R832g00=R=278%55%06R6#1#0#0#3;28C8%36C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e74 : bv 32 := 0x00000593.
Lemma D_103e74 : decode_any W_103e74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01D0#9R4P0P1g00B4g00<QR5#0R6#2R7#5R8%27#3g00=6R731g00=RR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e78 : bv 32 := 0x00150693.
Lemma D_103e78 : decode_any W_103e78 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01E>#9R4P0P1g00B4g00<QR5#0R6#3R7#5R8%35#0R9#3#1g00=6R:32%07#1=28:%09#5%15;2:C8%06#1C7,62R634R:P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e7c : bv 32 := 0x00068813.
Lemma D_103e7c : decode_any W_103e7c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01FL#9R4P0P1g00B4g00<QR5#0R6#2#5R7%06R6#0#0#3g00=6R831%25#0R5#2#3=178%05#5g00=R;18C8%36C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e80 : bv 32 := 0xfff6c683.
Lemma D_103e80 : decode_any W_103e80 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj12Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00DZj59Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=1g009GR0g00:3R1'CR2#BR3g01GZ#:R4P0P1g00FTg00G@g00<QR5#2R6#0#6%05R5#2R7#0#3g00=6R834R9P9%27#6%15#1#1#1#1#3;48D9%26#3C7,82R635R8P3P3%A3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_103e84 : bv 32 := 0x00d5e5b3.
Lemma D_103e84 : decode_any W_103e84 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Hh#8R4P0P1g00Q>g00<QR5#2R6#0R7#:R8%07#1g00=6R733R9P9%05#2#0#1=387C7%26#1C6,52R634R7P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e88 : bv 32 := 0x00f87663.
Lemma D_103e88 : decode_any W_103e88 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01J6#9R4P0P1g01:\g00<QR5#0R6#1#5R7%06R6#0#0#2g00=6R833%15R5#1#1#2=378%05R5#1#5%05#2;38C8%26C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e8c : bv 32 := 0x00180693.
Lemma D_103e8c : decode_any W_103e8c = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01KD#9R4P0P1g00B4g00<QR5#0R6#3#5R7%35#0R8#3#1g00=6R932%06R6#0#0#1=279%08#5%15;29C8%16C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e90 : bv 32 := 0xfee866e3.
Lemma D_103e90 : decode_any W_103e90 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01LR#9R4P0P1g010:g00<QR5#1R6#0#5R7%16R6#1#1#2g00=6R833%05R5#0R9#1#2=378%15#0#5%09#0#0#0#0#1#0#0#1#1#2;38C8%26C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e94 : bv 32 := 0x00c7fa63.
Lemma D_103e94 : decode_any W_103e94 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01M`#9R4P0P1g01:\g00<QR5#0R6#1R7#5R8%15R5#1#1#2g00=6R933%05R5#0#2=389%15#5%07#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e98 : bv 32 := 0x0007b683.
Lemma D_103e98 : decode_any W_103e98 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00DZj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Nn#9R4P0P1g00kdg00?ZR5g00<QR6#1R7#0#5R8%06R6#1R9#0#3g00=6R:32%06#0#3=28:%19#5g00=R;2:D8%17#3C7,62R734R:P3P3%:3P0g00>0P1g00>aC@,?2P4P7E<R7g00?:R4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103e9c : bv 32 := 0x00878793.
Lemma D_103e9c : decode_any W_103e9c = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01P<#9R4P0P1g00B4g00<QR5#0R6#1#5%15R5#1#1#2g00=6R733R8P8%05#0#5%06R6#0#2;37C8%26C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ea0 : bv 32 := 0x00b6e5b3.
Lemma D_103ea0 : decode_any W_103ea0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01QJ#8R4P0P1g00Q>g00<QR5#2R6#0R7#:R8%07#1g00=6R733R9%05#2#0#1=387P9C7%26#1C6,52R634R9P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ea4 : bv 32 := 0xfec7eae3.
Lemma D_103ea4 : decode_any W_103ea4 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01RX#9R4P0P1g010:g00<QR5#1R6#0#5R7%05R5#0#0R8#2g00=6R933%15R5#1#2=379%05#5%08#0#0#0#0#1#0#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ea8 : bv 32 := 0x02a66063.
Lemma D_103ea8 : decode_any W_103ea8 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Sf#9R4P0P1g010:g00<QR5#0R6#3R7#5R8%35#0R5#0#1g00=6R932%07#1=289%35#5%06R6#0#0#0#1;29C8%16C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103eac : bv 32 := 0x00e67e63.
Lemma D_103eac : decode_any W_103eac = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01U4#9R4P0P1g01:\g00<QR5#0R6#1#5R7%15R5#0R8#0#2g00=6R933%15#0R5#2=379%18#5%05#2;39C8%06#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103eb0 : bv 32 := 0x40c70733.
Lemma D_103eb0 : decode_any W_103eb0 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00@:j47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01VB#8R4P0P1g01WPg00<QR5#0R6#2#:R7%25R5#2#0#1g00=6R833R9P9%05#0#1=378C7%06#1C6,52R634R8P3P3%93P0g00>0P1g00>aC@,?2P4P6E;R6g00?:R4g00?ZR2'<1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103eb4 : bv 32 := 0x00064503.
Lemma D_103eb4 : decode_any W_103eb4 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00DZj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01X<#9R4P0P1g00FTg00G@g00<QR5#0R6#5R7#3R8%07#2g00=6R731%55#0#0R5#2=187%35g00=R;17D8%06#2C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103eb8 : bv 32 := 0xfff70713.
Lemma D_103eb8 : decode_any W_103eb8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00B`j49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=2g009GR0g00:3R1'CR2#BR3g01YJ#:R4P0P1g00B4g00<QR5#1R6#0#6%05R5#0R7#1#3g00=6R834R9P9%15#1#6%07#2#2#2#2#3;48C9%16#3C7,82R635R8P3P3%A3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_103ebc : bv 32 := 0x00a5e5b3.
Lemma D_103ebc : decode_any W_103ebc = Some (Op ALU_OR 11 11 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj11Tg002Hj14Tg002mj1:Tg003Kj10Tg003ij32Tg00@:j47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01ZX#8R4P0P1g00Q>g00<Q#1R5#4R6#:R7%46#0g00=6R832R9P9%16#0=278C7%15#0C6,52R533R8P3P3%93P0g00>0P1g00>aC@,?2P4P5E;R5g00?:R4g00?ZR2'<1=85=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ec0 : bv 32 := 0x00160613.
Lemma D_103ec0 : decode_any W_103ec0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01[f#9R4P0P1g00B4g00<QR5#0R6#5#3%55#0#0R7#1g00=6R832R9P9%37%15;28C8%06#1C7,62R634R8P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ec4 : bv 32 := 0xfe0718e3.
Lemma D_103ec4 : decode_any W_103ec4 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01]4#9R4P0P1g00MDg00<QR5#1R6#0#5R7%05R5#0R8#1#3g00=6R932g00=R=279%15#0#5%08#0#0#0#0#0#1#1#1#1#3;29C8%16#3C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ec8 : bv 32 := 0x0015b513.
Lemma D_103ec8 : decode_any W_103ec8 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01^B#9R4P0P1g01_Pg00<QR5#0R6#3R7#5R8%07#1g00=6R932%37#1=289%35#0#0#5%15;29C8%06#1C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ecc : bv 32 := 0x00813083.
Lemma D_103ecc : decode_any W_103ecc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00DZj58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01`<#9R4P0P1g00kdg00?ZR5g00<QR6#0R7#5#3R8%16g00=6R932%17=289%56#0#0#3%07R7#0#1;29D8%17C7,62R734R9P3P3%:3P0g00>0P1g00>aC@,?2P4P7E<R7g00?:R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ed0 : bv 32 := 0x01010113.
Lemma D_103ed0 : decode_any W_103ed0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00B`j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01aJ#9R4P0P1g00B4g00<QR5#0R6#5#3%16g00=6R732R8P8%55#0#0#3%06R6#0#0#1;27C8%16C7,62R634R7P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103ed4 : bv 32 := 0x00008067.
Lemma D_103ed4 : decode_any W_103ed4 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00N6j38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01bX#9R4P0P1g00<QR5#0R6#5#3R7g00=RR8g00=6R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00>0P1g00>aC@,?2P4P6E<R6g00?:R4g00?ZR2';1=96=442d3>o"). Qed.
