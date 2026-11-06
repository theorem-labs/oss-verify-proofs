(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanMemset_code () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC35stdpp9decidable;prod_eq_decI4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01K47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decidec69OSSVerify5KrLib2K55ASB02?AsanMemset_code;cl_fetch_bdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgITgt_bilateral_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee0cC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr05K47Corelib4Init9Datatypes4prod01c69OSSVerify5KrLib2K55ASB02?AsanMemset_code<cl_decode_bdC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee10C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr07K4ELinuxProcessSemantics5Riscv5Instr5msize01c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee14C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0:K4ELinuxProcessSemantics5Riscv5Instr5aluop01c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee18C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee1cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee20C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee24C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee28C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee2cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee30C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee34C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee38C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee3cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee40C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee44C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee48C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee4cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0=K4ELinuxProcessSemantics5Riscv5Instr5aluop02c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee50C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr09K4ELinuxProcessSemantics5Riscv5Instr5aluop03c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee54C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr01c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee58C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop0:c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee5cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee60C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee64C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee68C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee6cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee70C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0BK4ELinuxProcessSemantics5Riscv5Instr5mulop04c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee74C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee78C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee7cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee80C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee84C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee88C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee8cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee90C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee94C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee98C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bee9cC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beea0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beea4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beea8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beeacC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beeb0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beeb4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beeb8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beebcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beec0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beec4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beec8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beeccC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beed0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beed4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beed8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beedcC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop09c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beee0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beee4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize04c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beee8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beeecC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beef0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beef4C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beef8C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_beefcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanMemset_code7W_bef00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)
Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "h01ah14segsh21wp;1p;2p;3p;6g0000j1<Tg000Pj10Tg0015j11Tg001Sj12Tg0026j1;Tg002Xj2:Tg003Zj27Tg004<j34j15Tg004Vj16Tg005>j23Tg005[j68Tg0063j29Tg006[#<g007Z#0#0#0#0#0R0#0#1#2%10R0#2R1%;1R2f2f1':R3f0,71R434P2P2%52%60,31P3P4E8'9W2W0W1o"). Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "h01wh11xp;1p;2p;3p;4p;6g000Pj10Tg0015j1<Tg001Sj12Tg008?j21Tg0026j1;Tg008_j1:Tg003Zj23Tg004<j34j15Tg009Pj46Tg005>j27Tg005[j68Tg0063j29Tg007Z#0#0#0#0#0#<#2g009nR0g00:ZR1'1R2%;2R3f1#:R4f0,32R534P3P3%53P0g00;8P1g00;iC6,72P4P5E8'9W1W0o"). Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

(* [comment removed for export] *)
Definition W_bee0c : bv 32 := 0x0e060a63.
Lemma F_bee0c : fetch_word AsanUbsan.M.loaded_segments (0x1012a0 : word) = Some W_bee0c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#0#2#0#1#1#Ag00A:3;R1g00AVR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee0c : decode_any W_bee0c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj11Tg0015j14Tg00<gj12Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00AVR0g009nR1g00:ZR2g00F1g007ZR3#0R4#1#4R5%13R3#0R6#0#2g00A:R733g00Fc=357%16#4%13#1#0#1#0#0#2;37C<%04#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee10 : bv 32 := 0x00b50023.
Lemma F_bee10 : fetch_word AsanUbsan.M.loaded_segments (0x1012a4 : word) = Some W_bee10.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#1#2#0#2#0#Ag00A:3;R1g00GAR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee10 : decode_any W_bee10 = Some (Store SZ1 10 11 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00GAR0g009nR1g00:ZR2g00I2g007ZR3#0R4#2R5#4R6%05#1g00A:R733%25#1=367%23#0#0#4g00Fc;37C<%04#1C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee14 : bv 32 := 0x00c506b3.
Lemma F_bee14 : fetch_word AsanUbsan.M.loaded_segments (0x1012a8 : word) = Some W_bee14.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#0#2#0#2#0#1#Ag00A:3;R1g00I^R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee14 : decode_any W_bee14 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j1:Tg00<gj11Tg00=Ej33Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00I^R0g009nR1g00:ZR2g00KOg007ZR3#0R4#2R5#:R6%23#0R3#2#1g00A:R733%05#1=367%03#1=367C<%04#1C;R4g00B[R7g00C;R6'91712R3#6R5%50R01834R434P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=476d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee18 : bv 32 := 0x00300713.
Lemma F_bee18 : fetch_word AsanUbsan.M.loaded_segments (0x1012ac : word) = Some W_bee18.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#0#2#0#2#2#1#Ag00A:3;R1g00L;R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee18 : decode_any W_bee18 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00L;R0g009nR1g00:ZR2g00KOg007ZR3#0R4#2#4R5%23R3#2#0#1g00A:R633g00Fc=356%03#0#4%13;36C<%04#1C;R4g00B[R6g00C;R3':1912R5#7R7%60R01854R435P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=563d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee1c : bv 32 := 0xfeb68fa3.
Lemma F_bee1c : fetch_word AsanUbsan.M.loaded_segments (0x1012b0 : word) = Some W_bee1c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#1#2#2#0#0#Ag00A:3;R1g00MlR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee1c : decode_any W_bee1c = Some (Store SZ1 13 11 4095, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj12Tg00<Bj10Tg0015j15Tg00<gj13Tg00=Ej34Tg00HFj4=Tg00DGj4<Tg00=hj2;Tg008?j2:Tg0026j17Tg008_j18Tg003Zj29Tg004<j36j1CTg009Pj4BTg005>j2ATg005[j6@Tg00>Bj2>Tg00Dgj3?Tf0#0#0p=1g00MlR0g009nR1g00:ZR2g00I2g007ZR3#2R4#0R5#5R6%03R3#2R7#0#3g00A:R834%05#3=468%27#5%13#1#1#1#1#3;48C=%24#3C<R4g00B[R8g00C;R3';1:12R7#7R6%80R01974R436P6P6%C6P1g00;8P2g00;iCB,A7P0P4E@'>=683d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee20 : bv 32 := 0x0ee66063.
Lemma F_bee20 : fetch_word AsanUbsan.M.loaded_segments (0x1012b4 : word) = Some W_bee20.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#0#2#2#0#2#1#Ag00A:3;R1g00O1R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee20 : decode_any W_bee20 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00O1R0g009nR1g00:ZR2g00P6g007ZR3#0R4#2#4R5%23R3#0R6#0#1g00A:R733%23#0R3#1=357%26#4%03#0#0#0#1;37C<%04#1C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee24 : bv 32 := 0x00b500a3.
Lemma F_bee24 : fetch_word AsanUbsan.M.loaded_segments (0x1012b8 : word) = Some W_bee24.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#0#2#2#2#0#1#Ag00A:3;R1g00PhR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee24 : decode_any W_bee24 = Some (Store SZ1 10 11 1, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00PhR0g009nR1g00:ZR2g00I2g007ZR3#0R4#2R5#4R6%05#1g00A:R733%25#1=367%23#0#0#4%13;37C<%04#1C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee28 : bv 32 := 0x00b50123.
Lemma F_bee28 : fetch_word AsanUbsan.M.loaded_segments (0x1012bc : word) = Some W_bee28.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#0#1#0#1#1#1#1#2#Ag00A:3;R1g00QmR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee28 : decode_any W_bee28 = Some (Store SZ1 10 11 2, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00QmR0g009nR1g00:ZR2g00I2g007ZR3#0R4#2R5#4R6%05#1g00A:R733%25#1=367%23#0#0#4%14;37C<%04#1C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee2c : bv 32 := 0x00700713.
Lemma F_bee2c : fetch_word AsanUbsan.M.loaded_segments (0x1012c0 : word) = Some W_bee2c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#2#0#0#0#Ag00A:3;R1g00S2R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee2c : decode_any W_bee2c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00S2R0g009nR1g00:ZR2g00KOg007ZR3#0R4#2#4R5%23R3#2R6#0#1g00A:R733g00Fc=357%03#0#4%16;37C<%04#1C;R4g00B[R7g00C;R6':1912R3#7R5%60R01834R435P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=576d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee30 : bv 32 := 0xfeb68ea3.
Lemma F_bee30 : fetch_word AsanUbsan.M.loaded_segments (0x1012c4 : word) = Some W_bee30.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#2#1#0#2#0#Ag00A:3;R1g00T7R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee30 : decode_any W_bee30 = Some (Store SZ1 13 11 4093, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00T7R0g009nR1g00:ZR2g00I2g007ZR3#1R4#0R5#4R6%03R3#1R7#0#2g00A:R833%05#2=368%17#4%03#0#0#0#0#0#0#0#1#0#2;38C<%14#2C;R4g00B[R8g00C;R3':1912R7#7R6%60R01874R435P6P6%B6P1g00;8P2g00;iCA,@7P0P4E='>=583d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee34 : bv 32 := 0xfeb68f23.
Lemma F_bee34 : fetch_word AsanUbsan.M.loaded_segments (0x1012c8 : word) = Some W_bee34.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#2#0#2#1#0#Ag00A:3;R1g00U<R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee34 : decode_any W_bee34 = Some (Store SZ1 13 11 4094, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j15Tg00<gj13Tg00=Ej34Tg00HFj4=Tg00DGj4<Tg00=hj2;Tg008?j2:Tg0026j17Tg008_j18Tg003Zj29Tg004<j36j1CTg009Pj4BTg005>j2ATg005[j6@Tg00>Bj2>Tg00Dgj3?Tf0#0#0p=2g00U<R0g009nR1g00:ZR2g00I2g007ZR3#1R4#0R5#5R6%03R3#1R7#0#3g00A:R834%05#3=468%17#5%03#2#2#2#2#1#3;48C=%14#3C<R4g00B[R8g00C;R3';1:12R7#7R6%80R01974R436P6P6%C6P1g00;8P2g00;iCB,A7P0P4E@'>=683d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee38 : bv 32 := 0x0ce66463.
Lemma F_bee38 : fetch_word AsanUbsan.M.loaded_segments (0x1012cc : word) = Some W_bee38.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#2#1#1#0#1#1#0#Ag00A:3;R1g00VAR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee38 : decode_any W_bee38 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj11Tg0015j14Tg00<gj12Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00VAR0g009nR1g00:ZR2g00P6g007ZR3#0R4#1#4R5%13R3#0R6#0R7#2g00A:R833%13#0#2=358%16#4%17#0#0#0#2;38C<%04#2C;R4g00B[R8g00C;R7':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=587d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee3c : bv 32 := 0x00b501a3.
Lemma F_bee3c : fetch_word AsanUbsan.M.loaded_segments (0x1012d0 : word) = Some W_bee3c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#2#1#2#0#0#Ag00A:3;R1g00WFR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee3c : decode_any W_bee3c = Some (Store SZ1 10 11 3, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00WFR0g009nR1g00:ZR2g00I2g007ZR3#0R4#2R5#4R6%05#1g00A:R733%25#1=367%23R3#0#0#4%13;37C<%04#1C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee40 : bv 32 := 0x00900793.
Lemma F_bee40 : fetch_word AsanUbsan.M.loaded_segments (0x1012d4 : word) = Some W_bee40.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#2#0#2#0#2#1#Ag00A:3;R1g00XKR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee40 : decode_any W_bee40 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00XKR0g009nR1g00:ZR2g00KOg007ZR3#1R4#0#4R5%03R3#0#0#2g00A:R633g00Fc=356%13#1#4%14R4#0#2;36C<%24C;R4g00B[R6g00C;R3':1912R5#7R7%60R01854R435P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=563d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee44 : bv 32 := 0xfeb68e23.
Lemma F_bee44 : fetch_word AsanUbsan.M.loaded_segments (0x1012d8 : word) = Some W_bee44.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#2#0#2#2#0#1#Ag00A:3;R1g00YPR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee44 : decode_any W_bee44 = Some (Store SZ1 13 11 4092, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00YPR0g009nR1g00:ZR2g00I2g007ZR3#1R4#0R5#4R6%03R3#1R7#0#2g00A:R833%05#2=368%17#4%03#0#0#0#0#0#0#0#1#1#2;38C<%14#2C;R4g00B[R8g00C;R3':1912R7#7R6%60R01874R435P6P6%B6P1g00;8P2g00;iCA,@7P0P4E='>=583d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee48 : bv 32 := 0x0af66c63.
Lemma F_bee48 : fetch_word AsanUbsan.M.loaded_segments (0x1012dc : word) = Some W_bee48.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#0#1#1#0#1#1#1#2#Ag00A:3;R1g00ZUR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee48 : decode_any W_bee48 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00ZUR0g009nR1g00:ZR2g00P6g007ZR3#1R4#0R5#4R6%03R3#1R7#1#2g00A:R833%03#0#2=368%07#4%05#0#1#1#1#2;38C<%14#2C;R4g00B[R8g00C;R5':1912R7#7R6%60R01874R435P6P6%B6P1g00;8P2g00;iCA,@7P0P4E='>=585d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee4c : bv 32 := 0x40a006bb.
Lemma F_bee4c : fetch_word AsanUbsan.M.loaded_segments (0x1012e0 : word) = Some W_bee4c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#1#2#2#2#1#0#0#Ag00A:3;R1g00[ZR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee4c : decode_any W_bee4c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j1:Tg00<gj11Tg00=Ej33Tg00\_j4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00[ZR0g009nR1g00:ZR2g00]Kg007ZR3#0R4#2R5#:R6%23#0#2#1g00A:R333g00Fc=363%05#1=363C<%04#1C;R4g00B[R3g00C;R6'91712R5#6R7%50R01854R434P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=436d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee50 : bv 32 := 0x03859813.
Lemma F_bee50 : fetch_word AsanUbsan.M.loaded_segments (0x1012e4 : word) = Some W_bee50.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#2#1#1#1#0#1#0#Ag00A:3;R1g00^7R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee50 : decode_any W_bee50 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00_<j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00^7R0g009nR1g00:ZR2g00_hg007ZR3#0R4#2R5#4R6%04R4#0#0#1g00A:R733%25#1=367%23R3#0#4%23#0#0#0#1;37C<%14C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee54 : bv 32 := 0x101015b7.
Lemma F_bee54 : fetch_word AsanUbsan.M.loaded_segments (0x1012e8 : word) = Some W_bee54.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#0#2#2#2#0#2#0#1#Ag00A:3;R1g00`TR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee54 : decode_any W_bee54 = Some (Lui 11 65793, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;4p;6g000Pj11Tg00<Bj12Tg0015j14Tg00<gj13Tg00=Ej35Tg00aYj2=Tg00DGj4<Tg00=hj2;Tg008?j2:Tg0026j17Tg008_j18Tg003Zj29Tg004<j36j1CTg009Pj4BTg005>j2ATg005[j6@Tg00>Bj2>Tg00Dgj3?Tf0#1#1p=0g00`TR0g009nR1g00:ZR2g007Z#1R3#2R4#4%24#3g00A:R535%04#4%13R3#1#0#0#2#1#0#0#0#2#3;55'=%33C<R3g00B[R5g00C;R4';1:12R6#7R7%80R01963R336P7P7%C7P1g00;8P2g00;iCB,A6P0P3E@'>=654d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee58 : bv 32 := 0x0036f693.
Lemma F_bee58 : fetch_word AsanUbsan.M.loaded_segments (0x1012ec : word) = Some W_bee58.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#0#1#1#1#0#1#1#2#Ag00A:3;R1g00bER3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee58 : decode_any W_bee58 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j13Tg00<gj11Tg00=Ej35Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00bER0g009nR1g00:ZR2g00cJg007ZR3#0R4#2#3%23R3#0R5#2#1g00A:R635R7P7%05#3%13;56C<%04#1C;R4g00B[R6g00C;R3':1912R5#7R7%60R01854R434P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=463d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee5c : bv 32 := 0x00459713.
Lemma F_bee5c : fetch_word AsanUbsan.M.loaded_segments (0x1012f0 : word) = Some W_bee5c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#2#1#1#1#1#0#0#Ag00A:3;R1g00d6R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee5c : decode_any W_bee5c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00_<j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00d6R0g009nR1g00:ZR2g00_hg007ZR3#1R4#0R5#4R6%03R3#0#1#2g00A:R733%05#2=367%13#4%14#2R4;37C<P4C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee60 : bv 32 := 0x40d60633.
Lemma F_bee60 : fetch_word AsanUbsan.M.loaded_segments (0x1012f4 : word) = Some W_bee60.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#0#1#1#1#1#0#1#2#Ag00A:3;R1g00e;R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee60 : decode_any W_bee60 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j1:Tg00<gj11Tg00=Ej34Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j33j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00e;R0g009nR1g00:ZR2g00]Kg007ZR3#0R4#2#:R5%23#0R3#0#1g00A:R634R7P7%23#1=456C<%04#1C;R4g00B[R6g00C;R5'91712R3#6R7%50R01834R433P7P7%B7P1g00;8P2g00;iCA,@3P0P4E='>=365d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee64 : bv 32 := 0x00d505b3.
Lemma F_bee64 : fetch_word AsanUbsan.M.loaded_segments (0x1012f8 : word) = Some W_bee64.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#0#1#1#1#1#1#0#2#Ag00A:3;R1g00f@R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee64 : decode_any W_bee64 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj12Tg0015j1:Tg00<gj10Tg00=Ej33Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00f@R0g009nR1g00:ZR2g00KOg007ZR3#1R4#2R5#:R6%25#0g00A:R733%15#0=367%23#1#2#0=367C<%14#0C;R4g00B[R7g00C;R6'91712R3#6R5%50R01834R434P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=476d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee68 : bv 32 := 0x10070693.
Lemma F_bee68 : fetch_word AsanUbsan.M.loaded_segments (0x1012fc : word) = Some W_bee68.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj10Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=1g00?iR0g007ZR1#2#1#1R2#2#3%21#1#1#1#0#1#0#2#0#0#0#0#0#0#1#Ag00A:3;R1g00gER3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee68 : decode_any W_bee68 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00gER0g009nR1g00:ZR2g00KOg007ZR3#0R4#2#4R5%23R3#0R6#2#1g00A:R733%23#0#1=357%06#4%04R4#0#0#0#0#0#0#1;37C<%14C;R4g00B[R7g00C;R6':1912R5#7R3%60R01854R435P3P3%B3P1g00;8P2g00;iCA,@5P0P4E='>=576d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee6c : bv 32 := 0xffc67713.
Lemma F_bee6c : fetch_word AsanUbsan.M.loaded_segments (0x101300 : word) = Some W_bee6c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#0#0#0#0#Ag00A:3;R1g00hJR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee6c : decode_any W_bee6c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00hJR0g009nR1g00:ZR2g00cJg007ZR3#1R4#0#4R5%03R3#0R6#1#2g00A:R733%13#1R3#2=357%43%06#0#0#0#0#0#0#1#1#2;37C<%14#2C;R4g00B[R7g00C;R6':1912R3#7R5%60R01834R435P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=576d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee70 : bv 32 := 0x02d83633.
Lemma F_bee70 : fetch_word AsanUbsan.M.loaded_segments (0x101304 : word) = Some W_bee70.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#0#0#2#0#Ag00A:3;R1g00iOR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee70 : decode_any W_bee70 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j1:Tg00<gj11Tg00=Ej33Tg00jTj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00iOR0g009nR1g00:ZR2g00k@g007ZR3#0R4#2#:R5%23#0R3#0#1g00A:R633%04R4#0#0#1=356%23#1=356C<%14C;R4g00B[R6g00C;R5'91712R3#6R7%50R01834R434P7P7%B7P1g00;8P2g00;iCA,@3P0P4E='>=465d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee74 : bv 32 := 0x00c5a023.
Lemma F_bee74 : fetch_word AsanUbsan.M.loaded_segments (0x101308 : word) = Some W_bee74.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#0#0#2#1#0#Ag00A:3;R1g00klR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee74 : decode_any W_bee74 = Some (Store SZ4 11 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00klR0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43g00Fc;35C<%04#1C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee78 : bv 32 := 0x00e586b3.
Lemma F_bee78 : fetch_word AsanUbsan.M.loaded_segments (0x10130c : word) = Some W_bee78.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#0#1#1#0#Ag00A:3;R1g00m]R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee78 : decode_any W_bee78 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j1:Tg00<gj12Tg00=Ej33Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00m]R0g009nR1g00:ZR2g00KOg007ZR3#1R4#0R5#:R6%03R3#1#0#2g00A:R733%05#2=367%03#1#2=367C<%14#2C;R4g00B[R7g00C;R6'91712R3#6R5%50R01834R434P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=476d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee7c : bv 32 := 0xfec6ae23.
Lemma F_bee7c : fetch_word AsanUbsan.M.loaded_segments (0x101310 : word) = Some W_bee7c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#0#2#0#0#Ag00A:3;R1g00nbR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee7c : decode_any W_bee7c = Some (Store SZ4 13 12 4092, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00nbR0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#0#0#0#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee80 : bv 32 := 0x08f76063.
Lemma F_bee80 : fetch_word AsanUbsan.M.loaded_segments (0x101314 : word) = Some W_bee80.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#0#2#1#2#0#Ag00A:3;R1g00ogR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee80 : decode_any W_bee80 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj11Tg0015j14Tg00<gj12Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg00ogR0g009nR1g00:ZR2g00P6g007ZR3#0R4#1#4R5%13R3#1R6#0#2g00A:R733%16#2=357%03#1#4%04R4#0#0#0#0#0#2;37C<%24C;R4g00B[R7g00C;R3':1912R5#7R6%60R01854R435P6P6%B6P1g00;8P2g00;iCA,@5P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee84 : bv 32 := 0x00c5a223.
Lemma F_bee84 : fetch_word AsanUbsan.M.loaded_segments (0x101318 : word) = Some W_bee84.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#0#2#2#1#0#Ag00A:3;R1g010lR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee84 : decode_any W_bee84 = Some (Store SZ4 11 12 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg010lR0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%04#1R4;35C<P4C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee88 : bv 32 := 0x00c5a423.
Lemma F_bee88 : fetch_word AsanUbsan.M.loaded_segments (0x10131c : word) = Some W_bee88.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#2#0#1#1#1#0#Ag00A:3;R1g0121R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee88 : decode_any W_bee88 = Some (Store SZ4 11 12 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg0121R0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%04R4#0#1;35C<%14C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee8c : bv 32 := 0x01900793.
Lemma F_bee8c : fetch_word AsanUbsan.M.loaded_segments (0x101320 : word) = Some W_bee8c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#0#2#1#0#0#Ag00A:3;R1g0136R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee8c : decode_any W_bee8c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg0136R0g009nR1g00:ZR2g00KOg007ZR3#1R4#0#4R5%03R3#0#0#2g00A:R633g00Fc=356%13#1R3#4%03#2;36C<%14#2C;R4g00B[R6g00C;R3':1912R5#7R7%60R01854R435P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=563d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee90 : bv 32 := 0xfec6aa23.
Lemma F_bee90 : fetch_word AsanUbsan.M.loaded_segments (0x101324 : word) = Some W_bee90.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#1#0#1#0#Ag00A:3;R1g014;R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee90 : decode_any W_bee90 = Some (Store SZ4 13 12 4084, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg014;R0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#0#1#0#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee94 : bv 32 := 0xfec6ac23.
Lemma F_bee94 : fetch_word AsanUbsan.M.loaded_segments (0x101328 : word) = Some W_bee94.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#0#2#1#2#1#0#Ag00A:3;R1g015@R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee94 : decode_any W_bee94 = Some (Store SZ4 13 12 4088, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg015@R0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#0#0#1#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee98 : bv 32 := 0x06f76463.
Lemma F_bee98 : fetch_word AsanUbsan.M.loaded_segments (0x10132c : word) = Some W_bee98.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#1#2#1#1#0#Ag00A:3;R1g016ER3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee98 : decode_any W_bee98 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj11Tg0015j14Tg00<gj12Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg016ER0g009nR1g00:ZR2g00P6g007ZR3#0R4#1#4R5%13R3#1R6#0#2g00A:R733%16#2=357%03#1R3#4%03#0#0#2;37C<%04#2C;R4g00B[R7g00C;R3':1912R5#7R6%60R01854R435P6P6%B6P1g00;8P2g00;iCA,@5P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bee9c : bv 32 := 0x00c5a623.
Lemma F_bee9c : fetch_word AsanUbsan.M.loaded_segments (0x101330 : word) = Some W_bee9c.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#1#1#0#0#Ag00A:3;R1g017JR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bee9c : decode_any W_bee9c = Some (Store SZ4 11 12 12, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg017JR0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1R7=365%43?375C<%04#1C;R4g00B[R7g00C;R5':1912R3#7R6%60R01834R435P6P6%B6P1g00;8P2g00;iCA,@3P0P4E='>=575d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beea0 : bv 32 := 0x00c5a823.
Lemma F_beea0 : fetch_word AsanUbsan.M.loaded_segments (0x101334 : word) = Some W_beea0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#1#1#2#1#0#Ag00A:3;R1g018OR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beea0 : decode_any W_beea0 = Some (Store SZ4 11 12 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg018OR0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%04R4#0#0#1;35C<%14C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beea4 : bv 32 := 0x00c5aa23.
Lemma F_beea4 : fetch_word AsanUbsan.M.loaded_segments (0x101338 : word) = Some W_beea4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#1#1#1#2#0#Ag00A:3;R1g019TR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beea4 : decode_any W_beea4 = Some (Store SZ4 11 12 20, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg019TR0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R733%23#0#0R3#1=367%43%05#0#1;37C<%04#1C;R4g00B[R7g00C;R5':1912R3#7R6%60R01834R435P6P6%B6P1g00;8P2g00;iCA,@3P0P4E='>=575d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beea8 : bv 32 := 0x00c5ac23.
Lemma F_beea8 : fetch_word AsanUbsan.M.loaded_segments (0x10133c : word) = Some W_beea8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#0#1#1#1#1#0#Ag00A:3;R1g01:YR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beea8 : decode_any W_beea8 = Some (Store SZ4 11 12 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01:YR0g009nR1g00:ZR2g00m1g007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%03#1;35C<%04#1C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beeac : bv 32 := 0x0045f793.
Lemma F_beeac : fetch_word AsanUbsan.M.loaded_segments (0x101340 : word) = Some W_beeac.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#2#0#0#0#Ag00A:3;R1g01;^R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beeac : decode_any W_beeac = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01;^R0g009nR1g00:ZR2g00cJg007ZR3#1R4#0R5#4R6%03R3#0#0#2g00A:R733%05#2=367%13#1#4%14#2R4;37C<P4C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beeb0 : bv 32 := 0x02000813.
Lemma F_beeb0 : fetch_word AsanUbsan.M.loaded_segments (0x101344 : word) = Some W_beeb0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#2#1#0#2#0#Ag00A:3;R1g01<cR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beeb0 : decode_any W_beeb0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj15Tg0015j13Tg00<gj11Tg00=Ej32Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01<cR0g009nR1g00:ZR2g00KOg007ZR3#0R4#5#3R5%04R4#0#0R6#1g00A:R732g00Fc=257%53#0#0#3%06#1;27C<%14C;R4g00B[R7g00C;R6':1912R3#7R5%60R01834R434P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=476d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beeb4 : bv 32 := 0x01878793.
Lemma F_beeb4 : fetch_word AsanUbsan.M.loaded_segments (0x101348 : word) = Some W_beeb4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#2#0#2#1#0#Ag00A:3;R1g01=hR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beeb4 : decode_any W_beeb4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj11Tg0015j13Tg00<gj12Tg00=Ej35Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01=hR0g009nR1g00:ZR2g00KOg007ZR3#0R4#1#3%13R3#1#1#2g00A:R535R6P6%03#0R3#3%03#2;55C<%04#2C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R434P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=453d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beeb8 : bv 32 := 0x40f70733.
Lemma F_beeb8 : fetch_word AsanUbsan.M.loaded_segments (0x10134c : word) = Some W_beeb8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#2#1#0#1#1#0#Ag00A:3;R1g01>mR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beeb8 : decode_any W_beeb8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j1:Tg00<gj12Tg00=Ej34Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j33j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01>mR0g009nR1g00:ZR2g00]Kg007ZR3#1R4#0#:R5%03#0R3#1#2g00A:R634R7P7%03#2=456C<%14#2C;R4g00B[R6g00C;R5'91712R3#6R7%50R01834R433P7P7%B7P1g00;8P2g00;iCA,@3P0P4E='>=365d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beebc : bv 32 := 0xfec6a223.
Lemma F_beebc : fetch_word AsanUbsan.M.loaded_segments (0x101350 : word) = Some W_beebc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#2#1#2#0#0#Ag00A:3;R1g01@2R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beebc : decode_any W_beebc = Some (Store SZ4 13 12 4068, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01@2R0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#1#1#0#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beec0 : bv 32 := 0xfec6a423.
Lemma F_beec0 : fetch_word AsanUbsan.M.loaded_segments (0x101354 : word) = Some W_beec0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#2#0#2#0#2#0#2#1#Ag00A:3;R1g01A7R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beec0 : decode_any W_beec0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01A7R0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#1#0#1#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beec4 : bv 32 := 0xfec6a623.
Lemma F_beec4 : fetch_word AsanUbsan.M.loaded_segments (0x101358 : word) = Some W_beec4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#2#0#2#0#2#2#0#1#Ag00A:3;R1g01B<R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beec4 : decode_any W_beec4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01B<R0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#1#0#0#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beec8 : bv 32 := 0xfec6a823.
Lemma F_beec8 : fetch_word AsanUbsan.M.loaded_segments (0x10135c : word) = Some W_beec8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#1#0#1#0#1#1#1#2#Ag00A:3;R1g01CAR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beec8 : decode_any W_beec8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01CAR0g009nR1g00:ZR2g00m1g007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733%16R6#2=357%46%03#0#0#0#0#0#1#1#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beecc : bv 32 := 0x03076a63.
Lemma F_beecc : fetch_word AsanUbsan.M.loaded_segments (0x101360 : word) = Some W_beecc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#1#2#2#1#0#0#Ag00A:3;R1g01DFR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beecc : decode_any W_beecc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01DFR0g009nR1g00:ZR2g00P6g007ZR3#0R4#2#4R5%23R3#2#0#1g00A:R633%04R4#0#0#1=356%03#2R3#4%03#0#1;36C<%14C;R4g00B[R6g00C;R3':1912R5#7R7%60R01854R435P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=563d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beed0 : bv 32 := 0x02061613.
Lemma F_beed0 : fetch_word AsanUbsan.M.loaded_segments (0x101364 : word) = Some W_beed0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#2#1#1#0#1#0#Ag00A:3;R1g01EKR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beed0 : decode_any W_beed0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj13Tg0015j12Tg00<gj11Tg00=Ej35Tg00_<j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01EKR0g009nR1g00:ZR2g00_hg007ZR3#0R4#3#2%33#0R3#0#1g00A:R535R6P6%23%04R4#0#0#0#1;55C<%14C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R434P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=453d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beed4 : bv 32 := 0x00f585b3.
Lemma F_beed4 : fetch_word AsanUbsan.M.loaded_segments (0x101368 : word) = Some W_beed4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=1g00?iR0g007ZR1#0#1#1R2#0#3%01#1#1#1#2#1#2#2#0#2#2#0#2#0#1#Ag00A:3;R1g01FPR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beed4 : decode_any W_beed4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj12Tg00<Bj10Tg0015j1:Tg00<gj11Tg00=Ej34Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j33j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01FPR0g009nR1g00:ZR2g00KOg007ZR3#2R4#0R5#:R6%05#1g00A:R534R7P7%03#0#0#1=465C<%24#1C;R4g00B[R5g00C;R6'91712R3#6R7%50R01834R433P7P7%B7P1g00;8P2g00;iCA,@3P0P4E='>=356d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beed8 : bv 32 := 0x02065693.
Lemma F_beed8 : fetch_word AsanUbsan.M.loaded_segments (0x10136c : word) = Some W_beed8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#1#0#1#1#0#1#1#2#Ag00A:3;R1g01GUR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beed8 : decode_any W_beed8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00_<j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01GUR0g009nR1g00:ZR2g01HZg007ZR3#0R4#2#4R5%23#0R3#2#1g00A:R633%03#1=356%43%04R4#0#0#0#1;36C<%14C;R4g00B[R6g00C;R3':1912R5#7R7%60R01854R435P7P7%B7P1g00;8P2g00;iCA,@5P0P4E='>=563d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beedc : bv 32 := 0x00d66633.
Lemma F_beedc : fetch_word AsanUbsan.M.loaded_segments (0x101370 : word) = Some W_beedc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#2#1#1#1#0#0#Ag00A:3;R1g01IFR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beedc : decode_any W_beedc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j1:Tg00<gj11Tg00=Ej34Tg00Jcj4<Tg00DGj4;Tg00=hj29Tg008?j27Tg0026j16Tg008_j15Tg003Zj28Tg004<j33j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01IFR0g009nR1g00:ZR2g01JKg007ZR3#0R4#2#:R5%23#0R3#0#1g00A:R634R7P7%23#1=456C<%04#1C;R4g00B[R6g00C;R5'91712R3#6R7%50R01834R433P7P7%B7P1g00;8P2g00;iCA,@3P0P4E='>=365d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beee0 : bv 32 := 0x01f00693.
Lemma F_beee0 : fetch_word AsanUbsan.M.loaded_segments (0x101374 : word) = Some W_beee0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#1#0#1#1#1#0#1#2#Ag00A:3;R1g01K7R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beee0 : decode_any W_beee0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01K7R0g009nR1g00:ZR2g00KOg007ZR3#1R4#0#4R5%03R3#1R6#0#2g00A:R733g00Fc=357%16#4%03#0#0#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beee4 : bv 32 := 0x00c5b023.
Lemma F_beee4 : fetch_word AsanUbsan.M.loaded_segments (0x101378 : word) = Some W_beee4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj10Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#0#0p=2g00?iR0g007ZR1#0#2#2R2#0#3%01#2#2#2#1#2#1#1#0#1#1#1#1#0#2#Ag00A:3;R1g01L<R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beee4 : decode_any W_beee4 = Some (Store SZ8 11 12 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01L<R0g009nR1g00:ZR2g01MAg007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43g00Fc;35C<%04#1C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beee8 : bv 32 := 0x00c5b423.
Lemma F_beee8 : fetch_word AsanUbsan.M.loaded_segments (0x10137c : word) = Some W_beee8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj10Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=1g00?iR0g007ZR1#2#1#1R2#2#3%21#1#1#1#0#1#0#0#2#0#0#0#0#0#1#Ag00A:3;R1g01MmR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beee8 : decode_any W_beee8 = Some (Store SZ8 11 12 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01MmR0g009nR1g00:ZR2g01MAg007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%04R4#0#1;35C<%14C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beeec : bv 32 := 0x00c5b823.
Lemma F_beeec : fetch_word AsanUbsan.M.loaded_segments (0x101380 : word) = Some W_beeec.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#2#1#0#0#0#Ag00A:3;R1g01O2R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beeec : decode_any W_beeec = Some (Store SZ8 11 12 16, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01O2R0g009nR1g00:ZR2g01MAg007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%04R4#0#0#1;35C<%14C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beef0 : bv 32 := 0x00c5bc23.
Lemma F_beef0 : fetch_word AsanUbsan.M.loaded_segments (0x101384 : word) = Some W_beef0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#1#0#0#1#0#Ag00A:3;R1g01P7R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beef0 : decode_any W_beef0 = Some (Store SZ8 11 12 24, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j14Tg00<gj11Tg00=Ej33Tg00HFj4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01P7R0g009nR1g00:ZR2g01MAg007ZR3#0R4#2R5#4R6%25#1g00A:R533%23#0#0R3#1=365%43%03#1;35C<%04#1C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R435P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=553d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beef4 : bv 32 := 0xfe070713.
Lemma F_beef4 : fetch_word AsanUbsan.M.loaded_segments (0x101388 : word) = Some W_beef4.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj11Tg0015j13Tg00<Bj12Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#1#1p=0g00?iR0g007ZR1#1#0#0R2#1#3%11#0#0#0#2#0#2#2#2#1#0#2#1#0#Ag00A:3;R1g01Q<R3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beef4 : decode_any W_beef4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj11Tg0015j13Tg00<gj12Tg00=Ej35Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01Q<R0g009nR1g00:ZR2g00KOg007ZR3#0R4#1#3%13R3#1R5#0#2g00A:R635R7P7%03#0#3%15#1#1#1#0#0#0#0#0#2;56C<%04#2C;R4g00B[R6g00C;R5':1912R3#7R7%60R01834R434P7P7%B7P1g00;8P2g00;iCA,@3P0P4E='>=465d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beef8 : bv 32 := 0x02058593.
Lemma F_beef8 : fetch_word AsanUbsan.M.loaded_segments (0x10138c : word) = Some W_beef8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#1#2#0#1#1#0#Ag00A:3;R1g01RAR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beef8 : decode_any W_beef8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj12Tg0015j13Tg00<gj11Tg00=Ej35Tg00M@j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01RAR0g009nR1g00:ZR2g00KOg007ZR3#0R4#2R5#3%25#1g00A:R535R6P6%23#0#0#3%04R4#0#0#0#1;55C<%14C;R4g00B[R5g00C;R3':1912R6#7R7%60R01864R434P7P7%B7P1g00;8P2g00;iCA,@6P0P4E='>=453d3?o"). Qed.

(* [comment removed for export] *)
Definition W_beefc : bv 32 := 0xfee6e4e3.
Lemma F_beefc : fetch_word AsanUbsan.M.loaded_segments (0x101390 : word) = Some W_beefc.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#1#0#1#0#0#Ag00A:3;R1g01SFR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_beefc : decode_any W_beefc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj11Tg00<Bj10Tg0015j14Tg00<gj12Tg00=Ej33Tg00C[j4<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j35j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01SFR0g009nR1g00:ZR2g00P6g007ZR3#1R4#0#4R5%03R3#1#0R6#2g00A:R733%03R3#1#2=357%46%03#0#0#0#0#1#0#1#1#1#2;37C<%14#2C;R4g00B[R7g00C;R3':1912R6#7R5%60R01864R435P5P5%B5P1g00;8P2g00;iCA,@6P0P4E='>=573d3?o"). Qed.

(* [comment removed for export] *)
Definition W_bef00 : bv 32 := 0x00008067.
Lemma F_bef00 : fetch_word AsanUbsan.M.loaded_segments (0x101394 : word) = Some W_bef00.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;2p;6p;4g000Pj12Tg0015j13Tg00<Bj11Tg00<gj1ATg00=Ej3;Tg00=hj2:Tg001Sj18Tg0026j17Tg002Xj26Tg003Zj25Tg004<j34j19Tg004Vj1@Tg005>j2?Tg005[j6>Tg00>Bj2<Tg00>`j4=Tf0#2#2p=0g00?iR0g007ZR1#2#0#0R2#2#3%21#0#0#0#1#0#1#1#1#0#1#2#1#0#Ag00A:3;R1g01TKR3g00B[R4g00C;R5':%32R2#8R6#7R71601R11563R334P7P7%97%@2,?6P1P3E>'<=445dC=o"). Qed.
Lemma D_bef00 : decode_any W_bef00 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanMemset_code ()) [] "p;1p;3p;4p;2p;6g000Pj10Tg00<Bj13Tg0015j12Tg00=Ej31Tg00<gj15Tg01UPj3<Tg00DGj4;Tg00=hj2:Tg008?j29Tg0026j17Tg008_j16Tg003Zj28Tg004<j34j1BTg009Pj4ATg005>j2@Tg005[j6=Tg00>Bj2>Tg00Dgj3?Tg01TKR0g009nR1g00:ZR2g007ZR3#0R4#3#2R5g00FcR6g00A:R731%53=157%33#0#0#2?1673<%04#5C;R4g00B[R7g00C;R6':1912R3#7R5%60R01834R434P5P5%B5P1g00;8P2g00;iCA,@3P0P4E='>=476d3?o"). Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x1012a0%Z.
Definition Fo_000 := F_bee0c.
Definition Do_000 := D_bee0c.
Definition Fo_004 := F_bee10.
Definition Do_004 := D_bee10.
Definition Fo_008 := F_bee14.
Definition Do_008 := D_bee14.
Definition Fo_00c := F_bee18.
Definition Do_00c := D_bee18.
Definition Fo_010 := F_bee1c.
Definition Do_010 := D_bee1c.
Definition Fo_014 := F_bee20.
Definition Do_014 := D_bee20.
Definition Fo_018 := F_bee24.
Definition Do_018 := D_bee24.
Definition Fo_01c := F_bee28.
Definition Do_01c := D_bee28.
Definition Fo_020 := F_bee2c.
Definition Do_020 := D_bee2c.
Definition Fo_024 := F_bee30.
Definition Do_024 := D_bee30.
Definition Fo_028 := F_bee34.
Definition Do_028 := D_bee34.
Definition Fo_02c := F_bee38.
Definition Do_02c := D_bee38.
Definition Fo_030 := F_bee3c.
Definition Do_030 := D_bee3c.
Definition Fo_034 := F_bee40.
Definition Do_034 := D_bee40.
Definition Fo_038 := F_bee44.
Definition Do_038 := D_bee44.
Definition Fo_03c := F_bee48.
Definition Do_03c := D_bee48.
Definition Fo_040 := F_bee4c.
Definition Do_040 := D_bee4c.
Definition Fo_044 := F_bee50.
Definition Do_044 := D_bee50.
Definition Fo_048 := F_bee54.
Definition Do_048 := D_bee54.
Definition Fo_04c := F_bee58.
Definition Do_04c := D_bee58.
Definition Fo_050 := F_bee5c.
Definition Do_050 := D_bee5c.
Definition Fo_054 := F_bee60.
Definition Do_054 := D_bee60.
Definition Fo_058 := F_bee64.
Definition Do_058 := D_bee64.
Definition Fo_05c := F_bee68.
Definition Do_05c := D_bee68.
Definition Fo_060 := F_bee6c.
Definition Do_060 := D_bee6c.
Definition Fo_064 := F_bee70.
Definition Do_064 := D_bee70.
Definition Fo_068 := F_bee74.
Definition Do_068 := D_bee74.
Definition Fo_06c := F_bee78.
Definition Do_06c := D_bee78.
Definition Fo_070 := F_bee7c.
Definition Do_070 := D_bee7c.
Definition Fo_074 := F_bee80.
Definition Do_074 := D_bee80.
Definition Fo_078 := F_bee84.
Definition Do_078 := D_bee84.
Definition Fo_07c := F_bee88.
Definition Do_07c := D_bee88.
Definition Fo_080 := F_bee8c.
Definition Do_080 := D_bee8c.
Definition Fo_084 := F_bee90.
Definition Do_084 := D_bee90.
Definition Fo_088 := F_bee94.
Definition Do_088 := D_bee94.
Definition Fo_08c := F_bee98.
Definition Do_08c := D_bee98.
Definition Fo_090 := F_bee9c.
Definition Do_090 := D_bee9c.
Definition Fo_094 := F_beea0.
Definition Do_094 := D_beea0.
Definition Fo_098 := F_beea4.
Definition Do_098 := D_beea4.
Definition Fo_09c := F_beea8.
Definition Do_09c := D_beea8.
Definition Fo_0a0 := F_beeac.
Definition Do_0a0 := D_beeac.
Definition Fo_0a4 := F_beeb0.
Definition Do_0a4 := D_beeb0.
Definition Fo_0a8 := F_beeb4.
Definition Do_0a8 := D_beeb4.
Definition Fo_0ac := F_beeb8.
Definition Do_0ac := D_beeb8.
Definition Fo_0b0 := F_beebc.
Definition Do_0b0 := D_beebc.
Definition Fo_0b4 := F_beec0.
Definition Do_0b4 := D_beec0.
Definition Fo_0b8 := F_beec4.
Definition Do_0b8 := D_beec4.
Definition Fo_0bc := F_beec8.
Definition Do_0bc := D_beec8.
Definition Fo_0c0 := F_beecc.
Definition Do_0c0 := D_beecc.
Definition Fo_0c4 := F_beed0.
Definition Do_0c4 := D_beed0.
Definition Fo_0c8 := F_beed4.
Definition Do_0c8 := D_beed4.
Definition Fo_0cc := F_beed8.
Definition Do_0cc := D_beed8.
Definition Fo_0d0 := F_beedc.
Definition Do_0d0 := D_beedc.
Definition Fo_0d4 := F_beee0.
Definition Do_0d4 := D_beee0.
Definition Fo_0d8 := F_beee4.
Definition Do_0d8 := D_beee4.
Definition Fo_0dc := F_beee8.
Definition Do_0dc := D_beee8.
Definition Fo_0e0 := F_beeec.
Definition Do_0e0 := D_beeec.
Definition Fo_0e4 := F_beef0.
Definition Do_0e4 := D_beef0.
Definition Fo_0e8 := F_beef4.
Definition Do_0e8 := D_beef4.
Definition Fo_0ec := F_beef8.
Definition Do_0ec := D_beef8.
Definition Fo_0f0 := F_beefc.
Definition Do_0f0 := D_beefc.
Definition Fo_0f4 := F_bef00.
Definition Do_0f4 := D_bef00.
