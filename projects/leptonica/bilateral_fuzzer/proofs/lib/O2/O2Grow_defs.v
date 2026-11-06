(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall O2OpenFail_defs O2Open_defs O2Oom_defs O2DirRead_defs O2ReadLoop_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Grow_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs6g_sr1tC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4bool00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_r1nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs6cap2_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_r1tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_knMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_sr2C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib2O2;O2Grow_defs4g_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs6g_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs6g_kn3iC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_sr3C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib2O2;O2Grow_defs4g_r3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_knLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Grow_defs5g_srLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_LC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPSG : list Z := (0x17860 :: STOPSL)%Z.
Definition runG (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSG scr ss [].

(* [comment removed for export] *)
Definition g_ss1 : sym_state := SS 0x176ac sr_F [] kn_ML NXL.
Definition g_r1n := Eval vm_compute in runG (SCR [false] [] []) g_ss1.    (* [comment removed for export] *)
Definition g_r1t := Eval vm_compute in runG (SCR [true] [] []) g_ss1.     (* [comment removed for export] *)
Definition g_sr1 : list expr := Eval vm_compute in s_regs (fst (fst g_r1n)).
Definition g_kn1 : list kentry := Eval vm_compute in kn_after g_r1n kn_ML.
Definition g_sr1t : list expr := Eval vm_compute in s_regs (fst (fst g_r1t)).
Definition cap2_x : expr := Eval vm_compute in nth 10 g_sr1 (ELit 0).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition g_srM : list expr := sr_after_call_j g_sr1 KEPT_AL 41.
Definition g_knM : list kentry := Eval vm_compute in kn_acall g_kn1.
(* [comment removed for export] *)
Definition g_knOK : list kentry :=
  KRange (EVar 51) 0x6b000 0x7fffff7f0000 :: KAlign (EVar 51) 16 :: KWr (SA (EVar 51) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 51) 0) 65536 :: g_knM.

(* [comment removed for export] *)
Definition g_r2 := Eval vm_compute in runG (SCR [false; false] [] []) (SS 0x176c0 g_srM [] g_knOK 73).
Definition g_sr2 : list expr := Eval vm_compute in s_regs (fst (fst g_r2)).
Definition g_kn2 : list kentry := Eval vm_compute in kn_after g_r2 g_knOK.

(* [comment removed for export] *)
Definition g_sr3i : list expr := Eval vm_compute in sr_after_call_j g_sr2 KEPT_MC 73.
Definition g_kn3i : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x39000 g_kn2.
Definition g_r3 := Eval vm_compute in runG scr0 (SS 0x176dc g_sr3i [] g_kn3i 105).
Definition g_sr3 : list expr := Eval vm_compute in s_regs (fst (fst g_r3)).
Definition g_kn3 : list kentry := Eval vm_compute in kn_after g_r3 g_kn3i.

(* [comment removed for export] *)
Definition g_srL : list expr := Eval vm_compute in sr_after_call_j g_sr3 KEPT_AL 105.
Definition g_knL : list kentry := Eval vm_compute in kn_acall g_kn3.
Definition g_rvl : list expr := rvl9 (EVar 51) (EVar 8) cap2_x g_srL.

Section VP1.
Lemma g_itin1 :
  (s_pc (fst (fst g_r1n)), snd (fst g_r1n), s_log (fst (fst g_r1n)))
    = (0x2f94c%Z, [SCBr false BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ (nth 1 g_sr1 (ELit 0), nth 10 g_sr1 (ELit 0), nth 2 g_sr1 (ELit 0), nth 4 g_sr1 (ELit 0))
     = (ELit 0x176c0, cap2_x, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x49840)
  /\ cap2_x = EMd M_MUL (ELit 2) (EVar 8)
  /\ (s_pc (fst (fst g_r1t)), snd (fst g_r1t), s_log (fst (fst g_r1t)))
    = (0x17860%Z, [SCBr true BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ kn_after g_r1t kn_ML = kn_ML
  /\ (nth 2 g_sr1t (ELit 0), nth 3 g_sr1t (ELit 0), nth 4 g_sr1t (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x49840)
  /\ kn_vars_lt 41 g_kn1 = true /\ kn_acall g_kn1 = g_knM.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Grow_defs ()) ["VP1"] "p;1p;2p;3p;4g0000j1hTg000Pj2STg0010j17Tg001Oj1VTg002Xj11Tg003=j10Tg003bj3^Tg004kj1RTg0064j4pTg007Aj1fTg007aj3=Tg008Aj4;Tg008aj34Tg009;j3uTg00:Dj1cTg00:bj15Tg00;@j2iTg00<Kj3`Tg00=Vj2_Tg00>aj2PTg00?kj4yTg00A6j3xTg00BAj2dTg00CLj28Tg00Cgj2HTg00DAj4NTg00D\j3[Tg00E9j1kTg00F@j3mTg00F]j1nTg00Gej2tTg00Hej2sTg00Ilj1vTg00Jgj3jTg00L2j4oTf0R0#0#1#1#1p=W%10#1#0#0p=L%10#0#1#0p=T%00#1#1#0p=Q%00#5p=l%70#7p=a%10#0p=B%50#Rp=D%00#0#0#0p=3g00LNR1P1f1R2P0C;p=]f2R3P1P2P0C;p=F%00#0#1p=<%00#0#1#1p=>%10#0#0#0p=E%00#0#0#5p=2%10#1#1#1p=6%00#0#0#0#0#0#0#0p=:%00#0p=U%c0,P2p=rf3R4%c3'P?j20p=A%00#1p=Y%10#1#0#1p=K%10#1#1#0p=J%10#0#1p=z%10#1p=q%00#1#0#0p=g%00#0#1#0p=I%00#1#0#1p=C%10#0#1#1p=X%10#0#0#1p=@%10#0#1#0#0#1#1p=?1P43?j20p=\%52/d0p=eg00MWR5A=5207=3p=G1d32==50p=9A=520p=wf4A=5209=539=545=5p=OP1P2g00NbP0Cop=ZP1P2g00O[P0Cop=b%70#7#7#7p=Mg00PUR0g00Q3R2#hR4'SR3g00R@R6#hR7'SR8P3P7P0P4g00SKR9#W#L#T#Q#lg00T0g00TPR:g00UBg00UnR;#7R<#7R=#7R>#7R?#7R@#7RA#aRB#VRC%19RD#0RE#BRF#D3^RGg00VMRH#RRICp%f2RJ5=2C;%f6R6C;RK;4K1S11RL/S1RM/S1RN%W9#Q#L#3#DROg00Vk%09RP#DRQ;uCRC']g00WWRR%V;R;%0PRS#0RT#0RU#0RV#0RW#0RX#c#R3^RY5FL%<9#>#3#E#2RZ#RR[5FMR\;4\R]A41CCR^P3P7P0P4%09#6#3#L#2g00XCR_P:PGPICp==2JC;P6C;R6=486RJ%h5R2%5URG,i;R:%1DRD#1R`#6#6#6Ra#3#:#:#:#2%0X#3RX#3Rb#0#U#3Rc#0#3#:#:#25`;Rd1r;cRe%5cRc'_RfP;%0`#UPBPICAR`P;%UDRD#0Rg#0PBPICARhP;%UFPBPICARFP;%3EPBPICAREP;%1PRP#EPB%DV9^R;CARVP;%3PPB%Y9#K#E#Y#E#DCARPP;%ESPBPQCARQP;PWPB%DTRT9^R;CARRP;PgPB%09#J#6#K#E#DCARg%VARA%z9#Q#:#2R;%qa#6Ra#B#6#J#3#:#23`RW1iAGRG1PAHRA%5bRb'_PePcPAPbCy%BD#:#2,PI%B9#g#:#2'_%q9#I#K#J#2%19#B#C#X#L#Y#5%19#@#W#>#@#5%U9#@#W#>#@#5%<9#I#J#J#2%<9#>#3#X#2%?9#3#K#2PI%<9#I#J#6#2RDPB%RDC\PI%<9#I#6#>#2P?%V@R@C\%09#g#X#K#I#l%<9#I#6#J#2%<9#I#6#6#2%<9#>#3#I#2%<9#>#3#>#2%<9#>#3#Q#2%<9#>#3#T#2%19#g#L#Y#3#2%?9#C#C#2RD1PID?xT=%B9#@#T#X#3%?9#C#W#2'e%B9#@#T#L#@#5%?9#C#T#2RTPIPTPB%V>C\%B9#@#T#K#E%?9#C#L#2'e%?9#C#J#2%?9#C#6#2RTPIPTPB%5XRX#RC\%B9#@#X#:%?9#Q#Q#2'e%?9#K#K#2%59%5a5`@1dHX%f53G79;3G393G393G3959Z3939393G39393959b3GRb'w3GDODODORZ;4ZR;%EU#:#D,]Y=FL[RU=4MUR5g00XcRX?4__RHP:PdPfP`PhPFPEPVPPPQPRPgAGWGbDODODORb=42bRG'8RW'8Rg'8RR'8RQ'8RP'81H8KP]PP1HN\P^PQ1H1CPJPR1H86P;Pg1H2ZP5PW1HMUPHPG1HX_1H2bCNCNCNCNCNCNCNP3P7P0P4g00YCRb1Sb4RGg00ZQRHg00[]3[RW7[4R5#kAmb4WC;%n5C;=48K1Z<I%aBRB/ZI']1Z=I5FL1Z?I5FMP1P1POg00\VROC;=FLY=FM[54NA41OCP3P7P0P4g00]PR09[GHRH9[b4RG#kAmb4HC;%nGC;=486g00^IR6,t0=4261b=I1b>I']1b?I5FL=4MU%7B#a#M#M#M#M#M#M#Mg00_FRB's=4X_%vBg00`?542'8'8'8'8'8'8'8do"). Qed.

Lemma g_itin2 :
  (s_pc (fst (fst g_r2)), snd (fst g_r2), s_log (fst (fst g_r2))) = (0x36a58%Z, [SCBr false BC_EQ (EVar 8) (ELit 0)], [])
  /\ (nth 1 g_sr2 (ELit 0), nth 10 g_sr2 (ELit 0), nth 11 g_sr2 (ELit 0), nth 12 g_sr2 (ELit 0))
     = (ELit 0x176dc, EVar 51, EVar 6, EVar 8)
  /\ sr_vars_lt 73 g_sr2 = true /\ kn_vars_lt 73 g_kn2 = true
  /\ sr_after_call_j g_sr2 KEPT_MC 73 = g_sr3i /\ kn_call [] 0 0 IHI 0x39000 g_kn2 = g_kn3i /\ kn_vars_lt 73 g_kn3i = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Grow_defs ()) ["VP1"] "p;1p;2p;4p;3p;6g0000j1_Tg000Pj2OTg0010j12Tg001Oj1=Tg004kj1KTg0064j4nTg007Aj1XTg007aj34Tg008Aj4CTg008aj3ATg003=j10Tg00:Dj1dTg003bj3cTg002Xj11Tg009;j3oTg00:bj17Tg00<Kj3aTg00;@j2fTg00>aj2?Tg00?kj4lTg00=Vj2kTg00A6j3{Tg00BAj2NTg00CLj2>Tg00Cgj2WTg00DAj4RTg00D\j3hTg00E9j1uTg00F@j3tTg00F]j1sTg00a8j2rTg00Hej2gTg00b?j3qTg00cMj6vTg00Jgj3^Tg00L2j4pTf0R0#1#0p=:%10#1#0#1p=B%00#1#0#0p=6%10#0#1#1p=U%00#0#0#7p=3%20#2p=Z%00#1#1#1p=P%00#1#1#0p=E%10#1#0#0p=8%70#Kp=G%20#2#2#2p=[%20#2#2#2#2#2#2#2p=S%10#0#0#0p=;%00#0#0#0#0#0#0#0p=@%00#0#1p=M%00#0#1#1p=9%00#0#0#0p=5%10#0#0#1p=Yg00LNR1f1R2#=;40p=\f2R3#=%=2=410541p=JA41209413p=L%10#0#1p=I%10#1#1#1p=<%10#1p=m%10#1#1#0p=V%00#0p=`%d0,?2p=|%00#1p=e%00#1#0#1p=T%00#0#1#0p=H%72/N0p=zg00MWR4A4420743p=Q%03#7/N2=440p=Df3R5?^32=440p=j1N32=440p=y%02#7,N3=440p=if6f5f4R63^A^532=440544p=x1N651N32=440544p=w%d5,?6?^32=440p=FP1P2g00dRR2P0Cpp=]g00XcR3g00XCR67A0p=bg00PUR0g00Q3R5#_R7'OR8g00R@R9#_R:'OR;P8P:P0P7g00SKR<#:#B#6#U#3g00T0g00eKg00UnR=#2R>#2R?#2R@#2RA#2RB#2RC#ZRD#=REg00VMRF#KRGCn%X5545CC%X9CCR9;A91O11R5/O1RH/O1RIPHP1P5P1P1P1%P<#E#B#8#GRJ%ZDRK#2RL#2RM#2#[#S#SRN#2RO#2RP#2RQ#2#Z#[#SRR#=RSCC%=CRCCCPECCRT;ATRUAA366RV%_1RW%ZR#[#S#SRRg00WWRX%==R=%0<RY#0RZ#0R[#0R\#0R]#0R^#0R_#d#K3c%;\#@#G%M<#9#5#;#3R`#K%2R#[Ra%2aRa%2aRa%GYRb%[aRa#=%2aRa%2aRa%2aRa%2aRa%2aRa%2aRa%1<Rc#Gg00Vk?obE%1<#Y#P#9#Y#7Rd#K%=N%2a#Z#SRa%2aRa%2aRa%2a%X1'\3J5JQ9JOP5LC3L5LE,\?3J3J3J5LS7LS'\3J3L5LJ'\RJ;AJRE%_4RP%I<#E#@#3RO%1cRQ#1Ra#<#<#<RN#m#<Re#:#<#V#5#@#3Rf5aS%7\R\,fS%0_#5R_#5Rg#0#`#5Rh,|=Ri%7hRj1?SF%7gRgCl1f=\%5N#@#@#@#3%0h#5#@#@#35a=1kijP=%0a#`PDPGP=%`QRQ#0Ra#0PDPGP=%0cRc#;PDPGP=%5cPDPGP=%1YRY#;PD%G]9cX=P=%5YPD%e<#B#;#e#;#GP=%;ZPDPbP=P^PD%G[R[9cX=P=PaPD%0<#V#<#B#;#GAaCOf1fC\PiPj1?CFPgCl%:Q#@#3RQ,?G%:<#6#@#3'k%8<#U#P#;%1<#:#T#U#8#e#7Pd%`<#Y#P#9#Y#7%M<#H#V#V#3%0<#6#8#H#8%I<#9#5#B#3%M<#H#V#<#3Rd,?GPD%Kd%M<#H#<#9#3,?GPA%=BRB%0<#6#U#B#H%M<#H#<#V#3%0<#6#U#<#8%M<#9#5#H#3%0<#6#8#5#8%M<#9#5#E#3%0<#6#8#H#;%1<#6#8#6#5%I<#9#T#T#3RA1?GA?{[?%:<#:#E#:#U#5%I<#9#T#P#3'z%:<#:#E#:#8#Y#7%1<#6#B#E#:#3R[1?G[PD%=@%1<#6#B#E#8%I<#9#T#8#3%1<#6#B#P#;%I<#9#T#<#3R@1?G@PD%7_R_#K%1<#6#B#;#5%I<#9#E#E#3%1<#6#<#P#6%7<%7e5aB1NF_%X43Q7DO3DCj3D3DCj3y3Q3D5i`3D3D3DFx3DDw5ig3Q3QDFDFDFDFDFDFDFDFDF3Q3Q3QRg;AgR`/>VRO'>R4,>VR_'>RB'>1W;9PUPB1WITPVP_1W36R6PVP4P6PEPO1WWJP`PV1WPgP6CRCRCRCRCRCRP8P:P0P7g00YCR:1O:7g00ZQg00f=3hR87h7R6#uAt:78CC%s6CC=A;9PHP1P5P1P1P11]>G1]KGCC1]LGCC1]MGCC=AIT1rR2#bg00g5RT,gR#bg00gn=q2Rg00hm5AW1O00#XPFPFg00igPQPTEvg00jbRT5AP1gRT#b'>'>'>'>'>'>do"). Qed.

Lemma g_itin3 :
  (s_pc (fst (fst g_r3)), snd (fst g_r3), s_log (fst (fst g_r3))) = (0x2f80c%Z, [], [])
  /\ (nth 1 g_sr3 (ELit 0), nth 10 g_sr3 (ELit 0), nth 2 g_sr3 (ELit 0), nth 4 g_sr3 (ELit 0))
     = (ELit 0x176e4, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x49840)
  /\ kn_vars_lt 105 g_kn3 = true /\ kn_acall g_kn3 = g_knL
  /\ (sr_mismatch g_rvl idb g_srL sr_L 0, kn_missing g_knL (map (kmap g_rvl idb) kn_ML)) = ([0%nat], [KWr (SA (EVar 51) 0) 65536]).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Grow_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j1[Tg000Pj2MTg007Aj1ZTg008Aj4:Tg008aj3>Tg003=j10Tg004kj1<Tg0010j12Tg001Oj1QTg00:Dj1_Tg003bj3^Tg002Xj11Tg00<Kj3VTg00:bj14Tg00;@j2]Tg00>aj2?Tg00?kj4aTg00=Vj2\Tg00A6j3zTg00BAj2KTg007aj39Tg00CLj2ITg00Cgj2STg00DAj4YTg00D\j3dTg00E9j1qTg00F@j3pTg00F]j1oTg00Hej2mTg00Ilj1lTg00k\j5kTg00lij2jTg00moj4sTg00nKj2tTg00Jgj3XTg00L2j4uTf0R0#0#1#1#1p=E%10#1#0#0p=6%00#0#0#0p=5%00#1#1#0p=A%00#4p=c%10#1p=b%10#0#1#1p=G%00#0#1#0p=D%00#0#1p=J%00#0#1#1p=8%10#0#0#0p=F%00#0#0#4p=3%20#2p=`%20#2#2#2#2#2#2#2p=i%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=R%10#0#1p=H%00#0#0#0#0#0#0#0p=@%10#1#1#1p=;%10#0p==%10#1#1#0p=O%00#0p=Uf1R1%_0'?p=h%00#1p=g%10#1#0#1p=N%00#1#0#0p=7%00#1#0#1p=P%10#0#0#1p=T%41/K0p=yg00MWR2f2R3A921039p=L%03#4/K1=920p=Cf3R4?X31=920p=f1K31=920p=x%01#4,K3=920p=ef6f5f4R53XAX431=920592p=w1K541K31=920592p=v%_4,?5?X31=920p=BA9210p=rg00LNR3P1g00oWP0Cup=W%20#2#2#2p=ng00PUR0g00Q3R1#[R5'MR4g00R@R6#[R7'MR8P4P7P0P5g00SKR9#E#6#5#A#c%Z1C:%Z6C:R6;>61M33R1/M3R:/M3R;P:P3P1P3P3P3%09#b#G#E#D#c#<g00UnR<#2R=#2R>#2R?#2R@#2RA#2RB#QRCC:g00WWRD%Q<RE%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#_#<3^C:%J9#8#5#F#3RM#<C:RN;>NROg00XcRPg00XCRQ;>QRR%[2RS%`BRB#`RT#2#i#R#RRU#QRV%H9#A#@#3RW%19RX#1RY#1RZ#;#;#;R[#b#;R\#=#;#O#5#@#3R]3V%4IRI,]V%0L#5RL#5R^#0#U#5R_,hER`%4_Rag00VMRb,?VRV%4^R^Ca1]EI%5[#@#@#@#3%0_#5#@#@#35VE1\`aPE%0Z#UPB%<bRZPE%UYRY#0R_#0PBPZPE%0XRX#FPBPZPE%5XPBPZPE%1FRX#FPB%4J#<9^DEPE%5XPB%09#O#6#8#3#<PE%FGPB%4F#<PEPKPB%4H#<RH9^DEPEP_PB%g9#N#;#G#3#<AVCW]1]CIP`Pa1?CbP^Ca%=Y#@#3,?Z%=9#7#@#3'\%69#G#E#F%19#=#P#G#6#g#4%19#T#E#8#T#4%U9#T#E#8#T#4%J9#D#O#O#3%09#7#6#D#6%H9#8#5#N#3%J9#D#O#;#3RY,?ZPB%<Y%J9#D#;#8#3,?ZP@%QARA%09#7#G#N#D%J9#D#;#O#3%09#7#G#;#6%J9#8#5#D#3%09#7#6#5#6%J9#8#5#A#3%09#7#6#D#F%19#7#6#7#5%H9#8#P#P#3RY1?ZY?zH>%=9#=#A#=#G#5%H9#8#P#E#3'y%=9#=#A#=#6#T#4%19#7#N#A#=#3RH1?ZHPB%Q?%19#7#N#A#6%H9#8#P#6#3%19#7#N#E#F%H9#8#P#;#3R?1?Z?PB%4LRL#<%19#7#N#F#5%H9#8#A#A#3%19#7#;#E#7%49%4\5VA1KbL%Z2RL3L7CW3CCf3C3CCf3x3L3C5eM3C3C3CFw3CDv5e^3L3LDBDBDBDBDBDBDBDBDB3L3L3LRM;>MRWg010PRb#[RA/MSR\PAPS%Zb99b<1\V^/rLC:RL;>LR^'IRV'IRb'I1S86POPb1S;NPRPV1SPQPWP^1SSM1S\LCYCYCYCYP4P7P0P5g00YCR01M05g00ZQg010o3dR77d5R4#qAp057C:%o4C:=>86P:P3P1P3P3P31W=Z1WTZC:1W>ZC:1W@ZC:=>;N%`U#n#R#R#Rg011gRU'm=>PQ%lUg012`RU5>SPAPSg013YRSg014RRAg015Mg016FP<DkP2P21jSAg00^ICs,tUC:=>\L'I'I'I'Ido"). Qed.
End VP1.
