(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
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
Ltac2 kr_t_Sums2_codeK () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103cecC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr08c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103cf0C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5instr0:c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103cf4C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr06c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103cf8C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib4Init9Datatypes4bool02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103cfcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d04C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d08C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d0cC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d10C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d14C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d18C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d1cC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d20C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d24C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d28C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d2cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d30C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d34C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d38C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d3cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d40C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d44C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d48C13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d4cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d50C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d54C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5instr04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK8W_103d58C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa18C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa1cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa20C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa24C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa28C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa2cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa30C13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa34C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa38C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa3cC13~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa40C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa44C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa48C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa4cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa50C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa54C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa58C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa5cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa60C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa64C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa68C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa6cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa70C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa74C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa78C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa7cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa80C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa84C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa88C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa8cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa90C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa94C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa98C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaa9cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaa0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaa4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaa8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaacC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaab0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaab4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaab8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaabcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaac0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaac4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaac8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaccC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaad0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaad4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaad8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaadcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaae0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaae4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaae8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaecC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaf0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaf4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaaf8C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eaafcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab04C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab08C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab0cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab10C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab14C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab18C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab1cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab20C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab24C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab28C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab2cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab30C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab34C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab38C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab3cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab40C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab44C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab48C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab4cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab50C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab54C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab58C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab5cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab60C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab64C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab68C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab6cC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Sums2_codeK7W_eab70C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_103cec : bv 32 := 0x06060663.
Lemma D_103cec : decode_any W_103cec = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;`g00<RR5#0R6#1#5R7%15#0R5#0#3g00=7R832g00=S=278%15R5#5%15#0#0#3;28C8%06#3C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103cf0 : bv 32 := 0x00000693.
Lemma D_103cf0 : decode_any W_103cf0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@g#9R4P0P1g00B6g00<RR5#0R6#2#5R7%25#0R5#2#3g00=7R831g00=SR9=178%05#5?198C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103cf4 : bv 32 := 0x00d58733.
Lemma D_103cf4 : decode_any W_103cf4 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00CN#8R4P0P1g00B6g00<RR5#2R6#0R7#:R8%05R5#0#2#1g00=7R933%07#1=389%25#0#1=389C7%26#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103cf8 : bv 32 := 0x00074703.
Lemma D_103cf8 : decode_any W_103cf8 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00EI#9R4P0P1g00FXg00GDg00<RR5#0R6#1#5%15R5#1#0#3g00=7R732R8P8%05#0#5g00=S;27D8%06#3C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103cfc : bv 32 := 0x00070c63.
Lemma D_103cfc : decode_any W_103cfc = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Gd#9R4P0P1g00;`g00<RR5#0R6#1#5R7%15R5#1#0#3g00=7R832g00=S=278%05R5#1#5%05#0#3;28C8%06#3C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d00 : bv 32 := 0x00d507b3.
Lemma D_103d00 : decode_any W_103d00 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00I3#8R4P0P1g00B6g00<RR5#2R6#0R7#:R8%05R5#0#0#1g00=7R933%27#1=389%25#0#1=389C7%26#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d04 : bv 32 := 0x00168693.
Lemma D_103d04 : decode_any W_103d04 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00JB#9R4P0P1g00B6g00<RR5#0R6#1#5%15#0R7#1#2g00=7R833R9P9%07#5%25;38C8%06#2C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d08 : bv 32 := 0x00e78023.
Lemma D_103d08 : decode_any W_103d08 = Some (Store SZ1 15 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00L=#9R4P0P1g00FXg00<RR5#0R6#1#5R7%15R5#1R8#1#3g00=7R932%08#3=279%05#0#5g00=S;29C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d0c : bv 32 := 0xfed614e3.
Lemma D_103d0c : decode_any W_103d0c = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00ML#9R4P0P1g00N[g00<RR5#1R6#0#5R7%05R5#1R8#1#2g00=7R933%08R8#2=379%58%05#0#0#0#0#0#1#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d10 : bv 32 := 0x00060693.
Lemma D_103d10 : decode_any W_103d10 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00OM#9R4P0P1g00B6g00<RR5#0R6#2#5R7%25#0R5#2#3g00=7R831%05R5#3=178%55g00=S;18C8%06#3C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d14 : bv 32 := 0x00d505b3.
Lemma D_103d14 : decode_any W_103d14 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00P\#8R4P0P1g00B6g00<RR5#0R6#2R7#:R8%27#1g00=7R933%07#1=389%25#0#2#1=389C7%06#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d18 : bv 32 := 0x40d6073b.
Lemma D_103d18 : decode_any W_103d18 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00Qkj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00RW#8R4P0P1g00Sfg00<RR5#0R6#2#:R7%25R5#2#0#1g00=7R833%05R5#0#1=378%25#1=378C7%06#1C6,52R634R8P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d1c : bv 32 := 0x00b76733.
Lemma D_103d1c : decode_any W_103d1c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj12Tg002Hj10Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00TR#8R4P0P1g00Uag00<RR5#2R6#0R7#:R8%05#0#2#1g00=7R533R9P9%07#1=385C7%26#1C6,52R634R5P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=56=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d20 : bv 32 := 0x00f77713.
Lemma D_103d20 : decode_any W_103d20 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00VM#9R4P0P1g00W\g00<RR5#0R6#1#5%15R5#1R7#0#2g00=7R833R9P9%05#0#5%17#2;38C8%06#2C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d24 : bv 32 := 0x00070e63.
Lemma D_103d24 : decode_any W_103d24 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00XH#9R4P0P1g00;`g00<RR5#0R6#1#5R7%15R5#1#0R8#3g00=7R932g00=S=279%05#1#5%08#3;29C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d28 : bv 32 := 0x02d60863.
Lemma D_103d28 : decode_any W_103d28 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00YW#9R4P0P1g00;`g00<RR5#0R6#3#5R7%35#0R5#0R8#1g00=7R932%35R5#1=279%55%08#0#1;29C8%06#1C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d2c : bv 32 := 0x00c50633.
Lemma D_103d2c : decode_any W_103d2c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00Zf#8R4P0P1g00B6g00<RR5#0R6#4R7#:R8%45#0#0#1g00=7R532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d30 : bv 32 := 0x00058023.
Lemma D_103d30 : decode_any W_103d30 = Some (Store SZ1 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00\5#9R4P0P1g00FXg00<RR5#0R6#2R7#5R8%27#3g00=7R731g00=SR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d34 : bv 32 := 0x00158593.
Lemma D_103d34 : decode_any W_103d34 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00]D#9R4P0P1g00B6g00<RR5#0R6#1R7#5%17#2g00=7R733R8P8%15#0#0#5%25;37C8%06#2C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d38 : bv 32 := 0xfec59ce3.
Lemma D_103d38 : decode_any W_103d38 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00^S#9R4P0P1g00N[g00<RR5#1R6#0R7#5R8%07#2g00=7R733%05R5#1R9#1#2=387%09#5%05#0#0#0#0#0#0#0#1#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d3c : bv 32 := 0x01c0006f.
Lemma D_103d3c : decode_any W_103d3c = Some (Jal 0 28, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00_bj28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00`N#9R4P0P1g00<RR5#0R6#1R7#5g00=Sg00=7R833%07#1#5%15#1#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d40 : bv 32 := 0x00d60c63.
Lemma D_103d40 : decode_any W_103d40 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00a]#9R4P0P1g00;`g00<RR5#0R6#3#5R7%35#0R5#0R8#1g00=7R932%35R5#1=279%55%08#1;29C8%06#1C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d44 : bv 32 := 0x00c50633.
Lemma D_103d44 : decode_any W_103d44 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00bl#8R4P0P1g00B6g00<RR5#0R6#4R7#:R8%45#0#0#1g00=7R532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d48 : bv 32 := 0x0005b023.
Lemma D_103d48 : decode_any W_103d48 = Some (Store SZ8 11 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00d;#9R4P0P1g00eJg00<RR5#0R6#2R7#5R8%27#3g00=7R731g00=SR9=187%25#0#0#5?197C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d4c : bv 32 := 0x0005b423.
Lemma D_103d4c : decode_any W_103d4c = Some (Store SZ8 11 0 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00f6#9R4P0P1g00eJg00<RR5#0R6#2R7#5R8%27#3g00=7R731g00=S=187%25#0#0#5%06R6#0#3;17C8%36C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d50 : bv 32 := 0x01058593.
Lemma D_103d50 : decode_any W_103d50 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00gE#9R4P0P1g00B6g00<RR5#0R6#1R7#5%17#2g00=7R733R8P8%15#0#0#5%06R6#0#0#2;37C8%26C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d54 : bv 32 := 0xfec5eae3.
Lemma D_103d54 : decode_any W_103d54 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00hT#9R4P0P1g00icg00<RR5#1R6#0R7#5R8%07#2g00=7R733%05R5#1R9#1#2=387%09#5%05#0#0#0#0#0#0#1#0#1#1#2;37C8%16#2C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_103d58 : bv 32 := 0x00008067.
Lemma D_103d58 : decode_any W_103d58 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00jUj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00kA#9R4P0P1g00<RR5#0R6#5#3R7g00=SR8g00=7R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.



(* [comment removed for export] *)
Definition W_eaa18 : bv 32 := 0x00200613.
Lemma D_eaa18 : decode_any W_eaa18 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00lP#9R4P0P1g00B6g00<RR5#0R6#5#3R7%55#0#0R5#2g00=7R831g00=S=178%35%26;18C8%06#2C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa1c : bv 32 := 0x14c5ea63.
Lemma D_eaa1c : decode_any W_eaa1c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00m^#9R4P0P1g00icg00<RR5#0R6#1R7#5R8%17#2g00=7R933%15#0R5#0#2=389%15#5%07#1#0#1#0#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa20 : bv 32 := 0x00100613.
Lemma D_eaa20 : decode_any W_eaa20 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00nl#9R4P0P1g00B6g00<RR5#0R6#5#3R7%55#0#0R8#2g00=7R931g00=S=179%38%25;19C8%06#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa24 : bv 32 := 0x00100693.
Lemma D_eaa24 : decode_any W_eaa24 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g010:#9R4P0P1g00B6g00<RR5#0R6#2#5R7%25#0R8#2#3g00=7R931g00=S=179%08#5%35;19C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa28 : bv 32 := 0x00c0006f.
Lemma D_eaa28 : decode_any W_eaa28 = Some (Jal 0 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00_bj28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g011H#9R4P0P1g00<RR5#0R6#1R7#5g00=Sg00=7R833%07#1#5%15#0#0#2;38'8%06#2C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa2c : bv 32 := 0x00160613.
Lemma D_eaa2c : decode_any W_eaa2c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g012V#9R4P0P1g00B6g00<RR5#0R6#5#3%55#0#0R7#1g00=7R832R9P9%37%15;28C8%06#1C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa30 : bv 32 := 0x12b60c63.
Lemma D_eaa30 : decode_any W_eaa30 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g013d#9R4P0P1g00;`g00<RR5#1R6#0R7#5R8%05#1R5#1#2g00=7R933%07#2=389%05#5%16R6#0#0#0#1#1#1#2;39C8%26C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa34 : bv 32 := 0x00461713.
Lemma D_eaa34 : decode_any W_eaa34 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g015^#9R4P0P1g016lg00<RR5#0R6#2#5R7%25R5#2#0#3g00=7R831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa38 : bv 32 := 0x00e50733.
Lemma D_eaa38 : decode_any W_eaa38 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g017X#8R4P0P1g00B6g00<RR5#0R6#2R7#:R8%25#2#0#1g00=7R533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa3c : bv 32 := 0x00072703.
Lemma D_eaa3c : decode_any W_eaa3c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g018f#9R4P0P1g01:4g00?[R5g00<RR6#0R7#1#5%16R6#1#0#3g00=7R832R9P9%06#0#5g00=S;28D8%07#3C7,62R734R8P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa40 : bv 32 := 0x00060893.
Lemma D_eaa40 : decode_any W_eaa40 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01:`#9R4P0P1g00B6g00<RR5#0R6#2#5R7%06R6#0#2#3g00=7R831%25#0#0R5#3=178%55g00=S;18C8%36C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa44 : bv 32 := 0xfff88793.
Lemma D_eaa44 : decode_any W_eaa44 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj12Tg002mj16Tg003Kj13Tg003ij34Tg00@;j49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#2#2p=0g009GR0g00:3R1'CR2#BR3g01;n#:R4P0P1g00B6g00<RR5#1R6#2#6R7%25R5#0R8#3g00=7R934%16R6#1#2#3=479%15#1#6%08#0#0#0#3;49C9%36C7,82R635R9P3P3%A3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2'=1>96=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_eaa48 : bv 32 := 0x0017d813.
Lemma D_eaa48 : decode_any W_eaa48 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01=<#9R4P0P1g01>Jg00<RR5#0R6#1#5R7%06R6#0#0#2g00=7R833%15R9#1#1#2=378%09#5%25;38C8%26C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa4c : bv 32 := 0x00481293.
Lemma D_eaa4c : decode_any W_eaa4c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01?6#9R4P0P1g016lg00<RR5#0R6#5R7#3R8%27g00=7R731%06R6#0#0#2=187%55#0#3%26R6;17C8P6C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa50 : bv 32 := 0x005502b3.
Lemma D_eaa50 : decode_any W_eaa50 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j15Tg001cj11Tg002Hj1@Tg002mj18Tg003Kj10Tg003ij32Tg00Bbj46Tg0058j47Tg005Xj24Tg006:j33j19Tg006Tj4?Tg0072j2:Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01@D#5R4P0P1g00B6g00<R#1R5#@R6#8R7%06g00=7R832R9%16#0=278P9C6%15#0C7,42R533R9P3P3%93P0g00>1P1g00>bC?,:2P4P5E;R5g00?;R4g00?[R2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa54 : bv 32 := 0x0002a303.
Lemma D_eaa54 : decode_any W_eaa54 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01AR#9R4P0P1g01:4g00?[R5g00<RR6#0R7#5R8#3R9%56#0R6#2g00=7R:31%28=19:%06#3g00=S;1:D8%07#2C7,62R734R:P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa58 : bv 32 := 0xfce37ae3.
Lemma D_eaa58 : decode_any W_eaa58 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01B`#9R4P0P1g01Cng00<RR5#1R6#0#5R7%05R5#1R8#2g00=7R933%05R5#1#2=379%08#5%05#0#0#0#1#0#1#0#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa5c : bv 32 := 0x0002b303.
Lemma D_eaa5c : decode_any W_eaa5c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01D`#9R4P0P1g00eJg00?[R5g00<RR6#0R7#5R8#3R9%56#0R6#2g00=7R:31%28=19:%06#3g00=S;1:D8%07#2C7,62R734R:P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa60 : bv 32 := 0x00489893.
Lemma D_eaa60 : decode_any W_eaa60 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01En#9R4P0P1g016lg00<RR5#0R6#1#5%06R6#0#1#3g00=7R732R8P8%15#0#5%36R6;27C8P6C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa64 : bv 32 := 0x011508b3.
Lemma D_eaa64 : decode_any W_eaa64 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01G<#8R4P0P1g00B6g00<R#0R5#4R6#:R7%05R5#0#4#1g00=7R832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00>1P1g00>bC@,?2P4P5E;R5g00?;R4g00?[R2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa68 : bv 32 := 0x0048a383.
Lemma D_eaa68 : decode_any W_eaa68 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01HJ#9R4P0P1g01:4g00?[R5g00<RR6#0R7#1#5R8%16R6#1#3g00=7R932%07R7#0#1#3=289%06#0#5%37R7;29D8P7C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa6c : bv 32 := 0x0068b023.
Lemma D_eaa6c : decode_any W_eaa6c = Some (Store SZ8 17 6 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01IX#9R4P0P1g00eJg00<RR5#0R6#2#5R7%06R6#0#2#3g00=7R831%25#0R5#3=178%05#5g00=S;18C8%36C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa70 : bv 32 := 0x0082b303.
Lemma D_eaa70 : decode_any W_eaa70 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj11Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Jf#9R4P0P1g00eJg00?[R5g00<RR6#0R7#5R8#3R9%56#0R6#1g00=7R:32%18=29:%06#3%07R7#0#1;2:D8%17C7,62R734R:P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa74 : bv 32 := 0x0088be03.
Lemma D_eaa74 : decode_any W_eaa74 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01L4#9R4P0P1g00eJg00?[R5g00<RR6#0R7#1#5R8%16R6#1#0#0#2g00=7R933%07R7#0R:#1#2=389%06#0#5%2:;39D8%27C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa78 : bv 32 := 0x0068b423.
Lemma D_eaa78 : decode_any W_eaa78 = Some (Store SZ8 17 6 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01MB#9R4P0P1g00eJg00<RR5#0R6#3#5R7%06R6#0R8#3#1g00=7R932%35#0R5#1=279%05#5%18;29C8%16C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa7c : bv 32 := 0x00e2a023.
Lemma D_eaa7c : decode_any W_eaa7c = Some (Store SZ4 5 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01NP#9R4P0P1g01:4g00<RR5#0R6#2R7#5R8%37g00=7R731%25R5#2#0#3=187%05#0#5g00=S;17C8%06#3C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa80 : bv 32 := 0x0072a223.
Lemma D_eaa80 : decode_any W_eaa80 = Some (Store SZ4 5 7 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01O^#9R4P0P1g01:4g00<RR5#0R6#2R7#5R8%37g00=7R731%25R5#2#3=187%05#0#5%06#3R6;17C8P6C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa84 : bv 32 := 0x01c2b423.
Lemma D_eaa84 : decode_any W_eaa84 = Some (Store SZ8 5 28 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Pl#9R4P0P1g00eJg00<RR5#0R6#3R7#5R8%17g00=7R732%35R5#3#0#0#1=287%05#0#5%06R6#0#1;27C8%16C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa88 : bv 32 := 0x00080893.
Lemma D_eaa88 : decode_any W_eaa88 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01R:#9R4P0P1g00B6g00<RR5#0R6#2#5R7%06R6#0R8#2#3g00=7R931%08#3=179%25#0#0#5g00=S;19C8%36C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa8c : bv 32 := 0xfaf6ece3.
Lemma D_eaa8c : decode_any W_eaa8c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01SH#9R4P0P1g00icg00<RR5#1R6#0#5R7%05R5#1#0R8#2g00=7R933%05#0R5#2=379%58%05#0#1#0#0#0#1#1#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa90 : bv 32 := 0xf9dff06f.
Lemma D_eaa90 : decode_any W_eaa90 = Some (Jal 0 2097052, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj11Tg002Hj12Tg002mj14Tg003ij36Tg003Kj13Tg00_bj29Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#2#2p=0g009GR0g00:3R1'CR2#BR3g01TV#:R4P0P1g00<RR5#1R6#2R7#4g00=Sg00=7R836%17#2#4%25#0#0#0#0#0#0#1#1#2#0#1#1#3;68'9%16#3C7,82R635R8P3P3%A3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2'=1>86=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_eaa94 : bv 32 := 0x00000613.
Lemma D_eaa94 : decode_any W_eaa94 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Ud#9R4P0P1g00B6g00<RR5#0R6#5#2R7%55#0#0R5#3g00=7R831g00=SR9=178%25?198C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa98 : bv 32 := 0x00459693.
Lemma D_eaa98 : decode_any W_eaa98 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01W2#9R4P0P1g016lg00<RR5#1R6#0R7#5R8%05#1R5#0#3g00=7R932%07#3=289%55%16#3R6;29C8P6C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaa9c : bv 32 := 0x00d506b3.
Lemma D_eaa9c : decode_any W_eaa9c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01X@#8R4P0P1g00B6g00<RR5#0R6#2R7#:R8%25#0#2#1g00=7R533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaa0 : bv 32 := 0x0006b703.
Lemma D_eaaa0 : decode_any W_eaaa0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01YN#9R4P0P1g00eJg00?[R5g00<RR6#0R7#1#5R8%16R6#1#0#3g00=7R932%06R6#1#3=289%06#5g00=S;29D8%07#3C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaa4 : bv 32 := 0x0086b783.
Lemma D_eaaa4 : decode_any W_eaaa4 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01Z\#9R4P0P1g00eJg00?[R5g00<RR6#1R7#0#5R8%06R6#0#0#2g00=7R933%16R6#0#2=389%16#5%17R7#1#2;39D8%27C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaa8 : bv 32 := 0x00053803.
Lemma D_eaaa8 : decode_any W_eaaa8 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01[j#9R4P0P1g00eJg00?[R5g00<RR6#0R7#5R8#3R9%07R7#0#0#2g00=7R:31%08#2=19:%56#0#0#3g00=S;1:D8%27C7,62R734R:P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaac : bv 32 := 0x00853883.
Lemma D_eaaac : decode_any W_eaaac = Some (Load SZ8 true 17 10 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01]8#9R4P0P1g00eJg00?[R5g00<RR6#0R7#3R8#5R9%07R7#0R:#3#1g00=7R;32%08#1=29;%36#0#0#5%1:;2;D8%17C7,62R734R;P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=;7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaab0 : bv 32 := 0x00e53023.
Lemma D_eaab0 : decode_any W_eaab0 = Some (Store SZ8 10 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01^F#9R4P0P1g00eJg00<RR5#0R6#2R7#5R8%07#3g00=7R731%25R5#2#0#3=187%05#0#5g00=S;17C8%06#3C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaab4 : bv 32 := 0x00f53423.
Lemma D_eaab4 : decode_any W_eaab4 = Some (Store SZ8 10 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01_T#9R4P0P1g00eJg00<RR5#0R6#1R7#5R8%07#2g00=7R733%15R5#1#1#2=387%05#0#5%06R6#0#2;37C8%26C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaab8 : bv 32 := 0x0106b023.
Lemma D_eaab8 : decode_any W_eaab8 = Some (Store SZ8 13 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01`b#9R4P0P1g00eJg00<RR5#0R6#2#5R7%25#0R5#2#3g00=7R831%06R6#0#0#3=178%05#5g00=S;18C8%36C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaabc : bv 32 := 0x0116b423.
Lemma D_eaabc : decode_any W_eaabc = Some (Store SZ8 13 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01b0#9R4P0P1g00eJg00<RR5#0R6#1#5R7%15#0R5#1#2g00=7R833%06R6#0R9#1#2=378%05#5%29;38C8%26C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaac0 : bv 32 := 0x00000693.
Lemma D_eaac0 : decode_any W_eaac0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01c>#9R4P0P1g00B6g00<RR5#0R6#2#5R7%25#0R5#2#3g00=7R831g00=SR9=178%05#5?198C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaac4 : bv 32 := 0x00161793.
Lemma D_eaac4 : decode_any W_eaac4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01dL#9R4P0P1g016lg00<RR5#1R6#0#5R7%05R8#0#0#2g00=7R933%18R8#1#2=379%58%25;39C8%16#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaac8 : bv 32 := 0x00178813.
Lemma D_eaac8 : decode_any W_eaac8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01eZ#9R4P0P1g00B6g00<RR5#0R6#1#5R7%06R6#0#0#2g00=7R833%15R9#1#1#2=378%09#0#5%25;38C8%26C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaacc : bv 32 := 0x00461713.
Lemma D_eaacc : decode_any W_eaacc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01fh#9R4P0P1g016lg00<RR5#0R6#2#5R7%25R5#2#0#3g00=7R831%05R5#0#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaad0 : bv 32 := 0x00b86a63.
Lemma D_eaad0 : decode_any W_eaad0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01h6#9R4P0P1g00icg00<RR5#0R6#1R7#5R8%06R6#0#0#2g00=7R933%17#2=389%15#0#1#5%07#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaad4 : bv 32 := 0x00278793.
Lemma D_eaad4 : decode_any W_eaad4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01iD#9R4P0P1g00B6g00<RR5#1R6#0#5%05R5#0#0#2g00=7R733R8P8%15#1#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaad8 : bv 32 := 0x02b7ea63.
Lemma D_eaad8 : decode_any W_eaad8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01jR#9R4P0P1g00icg00<RR5#1R6#0R7#5R8%05R5#0#0#2g00=7R933%07#2=389%15#0R5#5%15#1#2;39C8%16#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaadc : bv 32 := 0x04c69c63.
Lemma D_eaadc : decode_any W_eaadc = Some (Branch BC_NE 13 12 88, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01k`#9R4P0P1g00N[g00<RR5#0R6#1R7#5R8%15#0R5#1R9#2g00=7R:33%05#2=38:%59%17#0#0#0#2;3:C8%06#2C7,62R634R:P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaae0 : bv 32 := 0x0880006f.
Lemma D_eaae0 : decode_any W_eaae0 = Some (Jal 0 136, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003ij33Tg003Kj12Tg00_bj28Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01ln#9R4P0P1g00<R#0R5#1R6#5g00=Sg00=7R733%06#1#5%05R5#0#1#0#0#0#2;37'8%25C7,62R534R7P3P3%:3P0g00>1P1g00>bC@,?2P4P5E<R5g00?;R4g00?[R2';1=75=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaae4 : bv 32 := 0x00e506b3.
Lemma D_eaae4 : decode_any W_eaae4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01n<#8R4P0P1g00B6g00<RR5#0R6#2R7#:R8%25R5#0#2#1g00=7R933%07#1=389%25#0#1=389C7%06#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaae8 : bv 32 := 0x00481893.
Lemma D_eaae8 : decode_any W_eaae8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g01oJ#9R4P0P1g016lg00<RR5#0R6#2#5R7%06R6#0R8#2#3g00=7R931%08#3=179%25#0#5%36R6;19C8P6C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaec : bv 32 := 0x011508b3.
Lemma D_eaaec : decode_any W_eaaec = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g020X#8R4P0P1g00B6g00<R#0R5#4R6#:R7%05R5#0#4#1g00=7R832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00>1P1g00>bC@,?2P4P5E;R5g00?;R4g00?[R2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaf0 : bv 32 := 0x0006a683.
Lemma D_eaaf0 : decode_any W_eaaf0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g021f#9R4P0P1g01:4g00?[R5g00<RR6#0R7#1#5%16#0R6#1#3g00=7R832R9P9%06#5g00=S;28D8%07#3C7,62R734R8P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaf4 : bv 32 := 0x0008a883.
Lemma D_eaaf4 : decode_any W_eaaf4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g0234#9R4P0P1g01:4g00?[R5g00<RR6#0R7#1#5%07R7#0#1#3g00=7R832R9P9%16#0#0#5g00=S;28D8%37C7,62R734R8P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaaf8 : bv 32 := 0x0116e463.
Lemma D_eaaf8 : decode_any W_eaaf8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g024B#9R4P0P1g00icg00<RR5#1R6#0#5R7%05#1#0R5#2g00=7R833%16R6#1R9#0#2=378%55%29;38C8%26C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eaafc : bv 32 := 0x00060813.
Lemma D_eaafc : decode_any W_eaafc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g025P#9R4P0P1g00B6g00<RR5#0R6#5#3R7%06R6#0#0#2g00=7R831%55#0#0R5#2=178%35g00=S;18C8%26C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab00 : bv 32 := 0x00080693.
Lemma D_eab00 : decode_any W_eab00 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g026^#9R4P0P1g00B6g00<RR5#0R6#2#5R7%25#0R5#2#3g00=7R831%06R6#0#0#3=178%05#5g00=S;18C8%36C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab04 : bv 32 := 0x00278793.
Lemma D_eab04 : decode_any W_eab04 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g027l#9R4P0P1g00B6g00<RR5#1R6#0#5%05R5#0#0#2g00=7R733R8P8%15#1#5%26;37C8%16#2C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab08 : bv 32 := 0xfcb7fae3.
Lemma D_eab08 : decode_any W_eab08 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g029:#9R4P0P1g01Cng00<RR5#1R6#0R7#5R8%05R5#0#0R9#2g00=7R:33%07#2=38:%15#0#5%09#0#0#1#0#1#0#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab0c : bv 32 := 0x00469813.
Lemma D_eab0c : decode_any W_eab0c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02:H#9R4P0P1g016lg00<RR5#0R6#2#5R7%06R6#0#0#3g00=7R831%25#0R5#2#3=178%55%36R6;18C8P6C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab10 : bv 32 := 0x00479893.
Lemma D_eab10 : decode_any W_eab10 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02;V#9R4P0P1g016lg00<RR5#1R6#0#5R7%16R6#1#0#3g00=7R832%05R5#0#0#3=278%15#5%36R6;28C8P6C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab14 : bv 32 := 0x01050833.
Lemma D_eab14 : decode_any W_eab14 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j15Tg001cj10Tg002Hj1@Tg002mj18Tg003Kj11Tg003ij32Tg00Bbj46Tg0058j47Tg005Xj24Tg006:j33j19Tg006Tj4?Tg0072j2:Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02<d#5R4P0P1g00B6g00<R#0R5#@R6#8R7%05R5#0#0#1g00=7R832R9%06#1=278P9C6%15C7,42R533R9P3P3%93P0g00>1P1g00>bC?,:2P4P5E;R5g00?;R4g00?[R2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab18 : bv 32 := 0x011508b3.
Lemma D_eab18 : decode_any W_eab18 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02>2#8R4P0P1g00B6g00<R#0R5#4R6#:R7%05R5#0#4#1g00=7R832R9%06#1=278P9C7%15C6,52R533R9P3P3%93P0g00>1P1g00>bC@,?2P4P5E;R5g00?;R4g00?[R2'<1=95=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab1c : bv 32 := 0x00082803.
Lemma D_eab1c : decode_any W_eab1c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003Kj13Tg003ij31Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02?@#9R4P0P1g01:4g00?[R5g00<RR6#0R7#5#2%07R7#0#0#3g00=7R831R9P9%56#0#0#2g00=S;18D8%37C7,62R734R8P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab20 : bv 32 := 0x0008a883.
Lemma D_eab20 : decode_any W_eab20 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02@N#9R4P0P1g01:4g00?[R5g00<RR6#0R7#1#5%07R7#0#1#3g00=7R832R9P9%16#0#0#5g00=S;28D8%37C7,62R734R8P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=87=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab24 : bv 32 := 0x01186463.
Lemma D_eab24 : decode_any W_eab24 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02A\#9R4P0P1g00icg00<RR5#0R6#1#5R7%06R6#0R8#0#2g00=7R933%18#2=379%15#0#1#5%28;39C8%26C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab28 : bv 32 := 0x00068793.
Lemma D_eab28 : decode_any W_eab28 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02Bj#9R4P0P1g00B6g00<RR5#1R6#0#5R7%05R5#0#0#3g00=7R832%15R5#0#3=278%15#5g00=S;28C8%16#3C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab2c : bv 32 := 0x00078693.
Lemma D_eab2c : decode_any W_eab2c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj13Tg003ij32Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02D8#9R4P0P1g00B6g00<RR5#1R6#0#5R7%05R5#1R8#0#3g00=7R932%05#0#3=279%18#5g00=S;29C8%16#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab30 : bv 32 := 0x02c78c63.
Lemma D_eab30 : decode_any W_eab30 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02EF#9R4P0P1g00;`g00<RR5#0R6#1#5R7%15R5#1R8#1#2g00=7R933%05R5#0#2=379%15#5%08#0#0#2;39C8%06#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab34 : bv 32 := 0x00469613.
Lemma D_eab34 : decode_any W_eab34 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg0152j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02FT#9R4P0P1g016lg00<RR5#0R6#2#5R7%25#0R5#0#3g00=7R831%25#3=178%55%06#3R6;18C8P6C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab38 : bv 32 := 0x00c50633.
Lemma D_eab38 : decode_any W_eab38 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj14Tg002mj1:Tg003Kj11Tg003ij32Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j33j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02Gb#8R4P0P1g00B6g00<RR5#0R6#4R7#:R8%45#0#0#1g00=7R532R9%07#1=285P9C7%06#1C6,52R633R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=342d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab3c : bv 32 := 0x00063783.
Lemma D_eab3c : decode_any W_eab3c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02I0#9R4P0P1g00eJg00?[R5g00<RR6#0R7#1#5R8%16R6#1#1#3g00=7R932%06#0R6#3=289%56g00=S;29D8%07#3C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab40 : bv 32 := 0x00e50733.
Lemma D_eab40 : decode_any W_eab40 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j18Tg001cj10Tg002Hj12Tg002mj1:Tg003Kj11Tg003ij33Tg00Bbj47Tg0058j46Tg005Xj25Tg006:j34j19Tg006Tj4@Tg0072j2?Tg007Oj6;Tg007gj2<Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02J>#8R4P0P1g00B6g00<RR5#0R6#2R7#:R8%25#2#0#1g00=7R533R9%07#1=385P9C7%06#1C6,52R634R9P3P3%93P0g00>1P1g00>bC@,?2P4P6E;R6g00?;R4g00?[R2'<1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab44 : bv 32 := 0x00073803.
Lemma D_eab44 : decode_any W_eab44 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02KL#9R4P0P1g00eJg00?[R5g00<RR6#0R7#2#5R8%07R7#0#0#3g00=7R931%26R6#2#0#3=189%06#0#5g00=S;19D8%37C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab48 : bv 32 := 0x00873883.
Lemma D_eab48 : decode_any W_eab48 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02LZ#9R4P0P1g00eJg00?[R5g00<RR6#0R7#1#5R8%07R7#0R9#1#2g00=7R:33%16R6#1#0#2=38:%06#0#5%29;3:D8%27C7,62R734R:P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=:7=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab4c : bv 32 := 0x00f73023.
Lemma D_eab4c : decode_any W_eab4c = Some (Store SZ8 14 15 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02Mh#9R4P0P1g00eJg00<RR5#0R6#1#5R7%15R5#1R8#0#3g00=7R932%18#3=279%05#0#5g00=S;29C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab50 : bv 32 := 0x00863783.
Lemma D_eab50 : decode_any W_eab50 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00D]j58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02O6#9R4P0P1g00eJg00?[R5g00<RR6#0R7#1#5R8%16R6#1#1#2g00=7R933%06#0R6#2=389%56%07R7#0#2;39D8%27C7,62R734R9P3P3%:3P0g00>1P1g00>bC@,?2P4P7E<R7g00?;R4/;51=97=445d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab54 : bv 32 := 0x00f73423.
Lemma D_eab54 : decode_any W_eab54 = Some (Store SZ8 14 15 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj12Tg003ij33Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02PD#9R4P0P1g00eJg00<RR5#0R6#1#5R7%15R5#1R8#0#2g00=7R933%18#2=379%05#0#5%06R6#0#2;39C8%26C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab58 : bv 32 := 0x01063023.
Lemma D_eab58 : decode_any W_eab58 = Some (Store SZ8 12 16 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj12Tg003ij31Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02QR#9R4P0P1g00eJg00<RR5#0R6#5#3R7%55#0#0R5#2g00=7R831%06R6#0#0#2=178%35g00=S;18C8%26C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab5c : bv 32 := 0x01163423.
Lemma D_eab5c : decode_any W_eab5c = Some (Store SZ8 12 17 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj13Tg002mj15Tg003Kj11Tg003ij32Tg00KQj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02R`#9R4P0P1g00eJg00<RR5#0R6#3#5R7%35#0#0R5#1g00=7R832%06R6#0R9#3#1=278%55%19;28C8%16C7,62R634R8P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=86=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab60 : bv 32 := 0x00068613.
Lemma D_eab60 : decode_any W_eab60 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003Kj13Tg003ij31Tg00@;j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02Sn#9R4P0P1g00B6g00<RR5#0R6#2#5R7%25#0R5#0R8#3g00=7R931%25#3=179%58g00=S;19C8%06#3C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab64 : bv 32 := 0xf6b6e0e3.
Lemma D_eab64 : decode_any W_eab64 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj11Tg002Hj10Tg002mj15Tg003Kj12Tg003ij33Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02U<#9R4P0P1g00icg00<RR5#1R6#0R7#5R8%05R5#1#0R9#2g00=7R:33%07#2=38:%59%05#0#0#1#0#0#1#1#1#1#1#2;3:C8%16#2C7,62R634R:P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=:6=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab68 : bv 32 := 0xfff58593.
Lemma D_eab68 : decode_any W_eab68 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2CTg000Pj1BTg0012j1:Tg001cj12Tg002Hj10Tg002mj16Tg003Kj13Tg003ij34Tg00@;j49Tg0058j47Tg005Xj28Tg006:j35j1ATg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2=Tg008Aj2>Tg008_j3;Tf0#0#0p=1g009GR0g00:3R1'CR2#BR3g02VJ#:R4P0P1g00B6g00<RR5#2R6#0R7#6%07#3g00=7R734R8P8%05R5#2#2#6%15#1#1#1#1#3;47C9%26#3C7,82R635R7P3P3%A3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2'=1>76=542d3;o"). Qed.

(* [comment removed for export] *)
Definition W_eab6c : bv 32 := 0xf20594e3.
Lemma D_eab6c : decode_any W_eab6c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003Kj13Tg003ij32Tg004Lj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02WX#9R4P0P1g00N[g00<RR5#0R6#1R7#5R8%17#3g00=7R732g00=S=287%15R5#0#1#5%15#1#1#0#0#1#0#1#0#0#0#3;27C8%06#3C7,62R634R7P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=76=442d3>o"). Qed.

(* [comment removed for export] *)
Definition W_eab70 : bv 32 := 0x00008067.
Lemma D_eab70 : decode_any W_eab70 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_Sums2_codeK ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003ij31Tg003Kj12Tg00jUj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g02Xf#9R4P0P1g00<RR5#0R6#5#3R7g00=SR8g00=7R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00>1P1g00>bC@,?2P4P6E<R6g00?;R4g00?[R2';1=96=442d3>o"). Qed.
