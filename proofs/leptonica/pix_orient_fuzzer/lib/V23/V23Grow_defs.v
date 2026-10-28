(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23OpenFail_defs V23Open_defs V23Oom_defs V23DirRead_defs V23ReadLoop_defs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Grow_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums8positive01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K47Corelib7Numbers7BinNums1Z03K47Corelib7Numbers7BinNums1Z02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs8kn_afterC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC5ARocqVerifyHarness?AgentSubmission3V23;V23Oom_defs8kn_acallK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01C47Corelib5Lists7ListDef3nthI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_sr1c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs6g_sr1tI47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4bool00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_r1nc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs6cap2_xc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_r1tC5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5kn_MLc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_kn1c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_knMC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:sr_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive?sr_after_call_jC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall7kn_callc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_sr2K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs4g_r2c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_kn2C5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs7KEPT_MCc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs6g_sr3iC5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3IHIc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs6g_kn3iC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_sr3I47Corelib4Init9Datatypes3nat00c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs4g_r3c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_kn3c5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_knLc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_rvlC5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission3V23<V23Grow_defs5g_srLC5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4sr_L".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSG : list Z := (0x63388 :: STOPSL)%Z.
Definition runG (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSG scr ss [].

(* [comment removed for export] *)
Definition g_ss1 : sym_state := SS 0x631d4 sr_F [] kn_ML NXL.
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
  KRange (EVar 51) 0x159000 0x7fffff7f0000 :: KAlign (EVar 51) 16 :: KWr (SA (EVar 51) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 51) 0) 65536 :: g_knM.

(* [comment removed for export] *)
Definition g_r2 := Eval vm_compute in runG (SCR [false; false] [] []) (SS 0x631e8 g_srM [] g_knOK 73).
Definition g_sr2 : list expr := Eval vm_compute in s_regs (fst (fst g_r2)).
Definition g_kn2 : list kentry := Eval vm_compute in kn_after g_r2 g_knOK.

(* [comment removed for export] *)
Definition g_sr3i : list expr := Eval vm_compute in sr_after_call_j g_sr2 KEPT_MC 73.
Definition g_kn3i : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x127000 g_kn2.
Definition g_r3 := Eval vm_compute in runG scr0 (SS 0x63204 g_sr3i [] g_kn3i 105).
Definition g_sr3 : list expr := Eval vm_compute in s_regs (fst (fst g_r3)).
Definition g_kn3 : list kentry := Eval vm_compute in kn_after g_r3 g_kn3i.

(* [comment removed for export] *)
Definition g_srL : list expr := Eval vm_compute in sr_after_call_j g_sr3 KEPT_AL 105.
Definition g_knL : list kentry := Eval vm_compute in kn_acall g_kn3.
Definition g_rvl : list expr := rvl9 (EVar 51) (EVar 8) cap2_x g_srL.

Section VP1.
Lemma g_itin1 :
  (s_pc (fst (fst g_r1n)), snd (fst g_r1n), s_log (fst (fst g_r1n)))
    = (0x10e958%Z, [SCBr false BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ (nth 1 g_sr1 (ELit 0), nth 10 g_sr1 (ELit 0), nth 2 g_sr1 (ELit 0), nth 4 g_sr1 (ELit 0))
     = (ELit 0x631e8, cap2_x, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ cap2_x = EMd M_MUL (ELit 2) (EVar 8)
  /\ (s_pc (fst (fst g_r1t)), snd (fst g_r1t), s_log (fst (fst g_r1t)))
    = (0x63388%Z, [SCBr true BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ kn_after g_r1t kn_ML = kn_ML
  /\ (nth 2 g_sr1t (ELit 0), nth 3 g_sr1t (ELit 0), nth 4 g_sr1t (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x1381d0)
  /\ kn_vars_lt 41 g_kn1 = true /\ kn_acall g_kn1 = g_knM.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Grow_defs ()) ["VP1"] "p;1p;2p;3p;4g0000j1jTg000Pj2PTg0010j10Tg001Uj18Tg0024j1VTg003=j11Tg003bj3]Tg004kj1QTg0064j4rTg007Aj1eTg007aj3?Tg008Aj4<Tg008aj34Tg009;j3uTg00:Dj1aTg00:bj15Tg00;@j2kTg00<Kj3^Tg00=Vj2iTg00>aj2TTg00?kj4|Tg00A6j3zTg00BAj2cTg00CLj27Tg00Cgj2HTg00DAj4NTg00D\j3YTg00E9j1pTg00F@j3oTg00F]j1nTg00Gej2vTg00Hgj2tTg00Inj1xTg00Jkj3mTg00L6j4lTf0R0#0#0#0#1p=@%10#1#0#1p=U%00#0#1#0p=9%10#0#1#1p=q%00#0#0#5p=2%80#8p=`%10#0p==%50#Qp=J%10#0#0#0p=3%10#1#0#0p=S%00#1#1#1p=Xg00LRR1P1f1R2P0C<p=\f2R3P1P2P0C<p=F%00#0#1#1#1p=L%00#0#0#0#0#0#1#1p=E%00#0p=G%00#1#1#0p=_%10#1#1#1p=:%00#0#0#0#0#0#0#0p=K%00#0#0#0#0#0#0#5p=I%00#0#0#0p=6%a0,T2p=sf3R4%a3'T?m20p=A%00#0#1#1p=h%00#1#0#0p=C%00#1#0#1#1p=g%10#1p=}%00#0#1p=f%10#0#0#1p=B%00#1#1#1#0#0#0#0p=[1T43?m20p=Z%00#1p=>%00#5p={%10#0#1#1#0#0#0#0p=O%00#1#0p=y%52/c0p=dg00M[R5A?5207?3p=D1c32=?50p=;A?520p=wf4A?5209?539?545?5p=RP1P2g00NfP0Clp=WP1P2g00OaP0Clp=b%80#8#8#8p=Mg00P]R0g00Q;R2#jR4'PR3g00RHR6#jR7'PR8P3P7P0P4g00SSR9#0#@#U#9#q#2g00T8g00TXR:g00UJg00V6R;#8R<#8R=#8R>#8R?#8R@#8RA#`RB#VRC%19RD#0RE#=RF#J3]RGg00VURH#QRICr%e2RJ5?2C<%e6R6C<RK;4K1P11RL/P1RM/P1RN%39#S#X#=#3#JROg00W3%09RP#JRQ;uCRC'\g00W_RR%V;R;%0PRS#0RT#0RU#0RV#0RW#0RX#a#Q3]RY5FL%L9#E#=#=#2RZ#QR[5FMR\;4\R]A41CCR^P3P7P0P4%19#G#_#X#@#2g00XKR_P:PGPICr=?2JC<P6C<R6=486RJ%j5R2%5URG,k;R:%1DRD#1R`#:#:#:Ra#K#K#K#I%0X#6RX#6Rb#0#G#6Rc#0#K#K#I5^;Rd1s;cRe%5cRc'iRfP;%0`#GPBPICAR`P;%0D#GRD#0PBPICARgP;%GFPBPICARFP;%0ERE#0#GPBPICARhP;%1PRP#3PB%JV9]R;CARVP;%6PPB%=9#h#@#C#6#JCARPP;%3SPBPQCARQP;PWPB%JTRT9]R;CARRP;PDPB%69#U#:#9#6#JCARD%VARA%g9#9#6#IR;%}a#:Ra#q#:#=#K#I3^RW1kAGRG1TAHRA%5bRb'iPePcPAPbC|%f9#h#=#6#I,TI%1E#G#6#I'i%09#C#:#U#3#2%G9#B#:#=#S#@#5%99#X#:#6#B#5%h9#X#:#6#B#5%09#[#9#I%L9#E#U#2%g9#E#:#2PI%09#[#9#@#2REPB%QECZPI%f9#S#6#B#>#2P?%V@R@CZ%09#[#9#_#=#{%L9#E#I%L9#E#@#2%L9#E#C#2%f9#S#6#U#>#2%L9#E#3#2%L9#E#S#2%09#O#C#9#2%09#O#3#3#2RE1TIE?zT=%>9#>#3#C#C#3%y9#S#9#9#=#2'd%>9#>#3#C#_#@#5%09#O#3#U#2RTPIPTPB%V>CZ%>9#>#3#C#[%09#O#3#:#2'd%09#O#B#@#2%09#O#B#9#2RTPIPTPB%5XRX#QCZ%>9#>#3#C#B#3%09#O#B#B#2'd%g9#@#@#9#2%59%5a5^@1cHX%e53D7;;3D3;3D3;3D3;5;Z3;3;3;3D3;3;3;5;b3DRb'w3DDRDRDRRZ;4ZR;%3U#K#J,\Y=FL[RU=4MUR5g00XkRX?4__RHP:PdPfP`PgPFPhPVPPPQPRPDADWGbDRDRDRRb=42bRG'7RW'7RD'7RR'7RQ'7RP'71H8KP]PP1HN\P^PQ1H1CPJPR1H86P;PD1H2ZP5PW1HMUPHPG1HX_1H2bCNCNCNCNCNCNCNP3P7P0P4g00YKRb1Pb4RGg00ZYRHg00[e3YRW7Y4R5#pAob4WC<%n5C<=48K1W<I%`BRB/WI'\1W=I5FL1W?I5FMP1P1POg00\`ROC<=FLY=FM[54NA41OCP3P7P0P4g00]\R09YGHRH9Yb4RG#pAob4HC<%nGC<=486g00^WR6,v0=4261b=I1b>I'\1b?I5FL=4MU%8B#`#M#M#M#M#M#M#Mg00_VRB't=4X_%xBg00`Q542'7'7'7'7'7'7'7do"). Qed.

Lemma g_itin2 :
  (s_pc (fst (fst g_r2)), snd (fst g_r2), s_log (fst (fst g_r2))) = (0x11e154%Z, [SCBr false BC_EQ (EVar 8) (ELit 0)], [])
  /\ (nth 1 g_sr2 (ELit 0), nth 10 g_sr2 (ELit 0), nth 11 g_sr2 (ELit 0), nth 12 g_sr2 (ELit 0))
     = (ELit 0x63204, EVar 51, EVar 6, EVar 8)
  /\ sr_vars_lt 73 g_sr2 = true /\ kn_vars_lt 73 g_kn2 = true
  /\ sr_after_call_j g_sr2 KEPT_MC 73 = g_sr3i /\ kn_call [] 0 0 IHI 0x127000 g_kn2 = g_kn3i /\ kn_vars_lt 73 g_kn3i = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V23Grow_defs ()) ["VP1"] "p;1p;2p;4p;3p;6g0000j1_Tg000Pj2TTg0010j10Tg001Uj11Tg0024j1?Tg004kj1KTg0064j4lTg007Aj1[Tg007aj34Tg008Aj4BTg008aj3@Tg00:Dj1bTg003bj3cTg003=j13Tg009;j3mTg00:bj15Tg00<Kj3\Tg00;@j2dTg00>aj2ATg00?kj4jTg00=Vj2iTg00A6j3zTg00BAj2NTg00CLj2>Tg00Cgj2YTg00DAj4VTg00D\j3fTg00E9j1tTg00F@j3sTg00F]j1qTg00aLj2pTg00Hgj2eTg00bSj3oTg00caj6nTg00Jkj3^Tg00L6j4wTf0R0#0#0#3#3p=8%30#3#0#0p=6%00#0#3#0p=:%30#0p=7%00#5p=r%10#1p=X%00#0#0#0p=2%00#3#0#0p=;%50#Kp=I%10#1#1#1p=Z%10#1#1#1#1#1#1#1p=W%30#0#0#0p=<%00#0#0#0#0#0#0#0p=L%00#3#3#3p=C%00#0#0#5p==%30#3#3#3p=9%30#0#0#3p=Hg00LRR1f1R2#?;40p=]f2R3#?%?2=410541p=JA41209413p=O%30#0#3#3p=P%00#0#0#0#0#0#0#5p=G%30#3p=k%00#0p=U%b0,A2p={%00#0#0#3p=S%00#3p=F%00#0#3p=Q%00#3#0p=R%52/N0p=yg00M[R4A4420743p=M%03#5/N2=440p=Ef3R5?^32=440p=h1N32=440p=x%02#5,N3=440p=gf6f5f4R63^A^532=440544p=v1N651N32=440544p=u%b5,A6?^32=440p=DP1P2g00dfR2P0Cwp=`g00XkR3g00XKR67@0p=ag00P]R0g00Q;R5#_R7'TR8g00RHR9#_R:'TR;P8P:P0P7g00SSR<#0#8#6#:#7#7#7#rg00T8g00eag00V6R=#1R>#1R?#1R@#1RA#1RB#1RC#XRD#?REg00VURF#KRGCl%[5545CB%[9CBR9;@91T11R5/T1RH/T1RIPHP1P5P1P1P1%7<#8#:#2#;#IRJ%XDRK#1RL#1RM#1#Z#W#WRN#1RO#1RP#1RQ#1#X#Z#WRR#?RSCB%?CRCCBPECBRT;@TRUA@366RV%_1RW%XR#Z#W#WRRg00W_RX%?=R=%0<RY#0RZ#0R[#0R\#0R]#0R^#0R_#b#K3c%<\#L#I%0<#C#2#8#7#7#=R`#K%1R#ZRa%1aRa%1aRa%IYRb%ZaRa#?%1aRa%1aRa%1aRa%1aRa%1aRa%1aRa%3<Rc#Ig00W3?mbE%:<#C#9#2#H#5Rd#K%?N%1a#X#WRa%1aRa%1aRa%1a%[1']3J5JQ9JOP5OC3O5OE,]?3J3J3J5OS7OS']3J3O5OJ']RJ;@JRE%_4RP%0<#P#:#2#GRO%3cRQ#3Ra#9#9#9RN#k#9Re#P#9#7#L#GRf5\S%5\R\,dS%0_#2R_#2Rg#0#U#2Rh,{=Ri%5hRj1ASF%5gRgCj1d=\%LN#L#L#G%0h#L#L#G5\=1iijP=%0a#UPDPGP=%0Q#URQ#0PDPGP=%0cRc#<PDPGP=%0cRc#0#UPDPGP=%3YRY#<PD%I]9cX=P=%2YPD%7<#8#S#;#2#IP=%<ZPDPbP=P^PD%I[R[9cX=P=PQPD%U<#8#F#9#:#2#IA\COf1dC\PiPj1ACFPgCj%Q<#8#7#2#GRC,AG%3c#U#2#G'i%Q<#8#9#F#7#2%U<#H#9#7#6#S#5Pd%8<#C#9#2#H#5%0<#C#2#:#G%Q<#6#2#9#;%0<#P#2#8#9#=%0<#C#2#:#S#=Rd,AGPD%Kd%Q<#6#2#H#F#=,AGPA%?BRB%Q<#6#2#H#7#7%0<#C#2#8#G%Q<#6#2#6#;%0<#C#2#8#;#=%0<#C#2#8#F#;%0<#C#2#8#<#=%Q<#6#2#9#2%R<#6#S#2#<%0<#P#2#<#<#=RA1AGA?z[?%F<#F#<#;#;#<%R<#6#:#:#7#='y%F<#F#7#S#S#7#S#5%R<#6#:#8#F#=R[1AG[PD%?@%R<#6#:#8#<%0<#P#2#<#9#=%R<#6#:#;#;%0<#P#2#H#:#=R@1AG@PD%5_R_#K%R<#6#:#;#6%0<#P#2#H#H#=%R<#6#;#;#<%5<%5e5\B1NF_%[43M7EO3ECh3E3ECh3x3M3E5g`3E3E3EFv3EDu5gg3M3MDDDDDDDDDDDDDDDDDD3M3M3MRg;@gR`/>VRO'>R4,>VR_'>RB'>1Y;9PUPB1YITPVP_1Y36R6PVP4P6PEPO1YWJP`PV1YPgP6CVCVCVCVCVCVP8P:P0P7g00YKR:1T:7g00ZYg00fS3fR87f7R6#tAs:78CB%q6CB=@;9PHP1P5P1P1P11`>G1`KGCB1`LGCB1`MGCB=@IT1pR2#ag00gMRT,eR#ag00hH=o2Rg00iI5@W1T00#[PFPFg00jEPCPTEng00kBRT5@P1eRT#a'>'>'>'>'>'>do"). Qed.

Lemma g_itin3 :
  (s_pc (fst (fst g_r3)), snd (fst g_r3), s_log (fst (fst g_r3))) = (0x10e818%Z, [], [])
  /\ (nth 1 g_sr3 (ELit 0), nth 10 g_sr3 (ELit 0), nth 2 g_sr3 (ELit 0), nth 4 g_sr3 (ELit 0))
     = (ELit 0x6320c, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ kn_vars_lt 105 g_kn3 = true /\ kn_acall g_kn3 = g_knL
  /\ (sr_mismatch g_rvl idb g_srL sr_L 0, kn_missing g_knL (map (kmap g_rvl idb) kn_ML)) = ([0%nat], [KWr (SA (EVar 51) 0) 65536]).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Grow_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j1ZTg000Pj2MTg007Aj1WTg008Aj4=Tg008aj3?Tg003=j11Tg004kj1>Tg001Uj12Tg0024j1UTg0010j10Tg00:Dj1`Tg003bj3_Tg00<Kj3VTg00:bj14Tg00;@j2]Tg00>aj2@Tg00?kj4cTg00=Vj2\Tg00A6j3zTg00BAj2HTg007aj3;Tg00CLj2KTg00Cgj2TTg00DAj4XTg00D\j3dTg00E9j1qTg00F@j3pTg00F]j1oTg00Hgj2mTg00Inj1lTg00l>j5kTg00mKj2sTg00nQj4tTg00nmj2jTg00Jkj3[Tg00L6j4xTf0R0#0#0#0p=O%00#1#1#1p=^%00#1p=C%00#0#0#0p=3%00#0#1#1p=<%00#0#0#4p=5%00#0#0#1p=R%10#0#0#1p=G%00#1#1#0p=Q%00#4p={%00#0#1#1#1#0#0#0#0p=F%10#0p=E%20#2p=a%20#2#2#2#2#2#2#2p=i%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=S%10#0#1#1p=J%00#0#1#0p=9%00#0#0#0#0#0#0#4p=D%10#1#1#1p=6%10#1p=h%00#0#0#0#0#0#0#0p=Nf1R1%`0'@p=g%10#0#0#0p=7%00#0p=b%00#1#0#0p=:%00#0#1p=P%10#1#0#0p=8%00#1#0p=I%41/H0p=yg00M[R2f2R3A;2103;p=L%03#4/H1=;20p=Af3R4?[31=;20p=f1H31=;20p=w%01#4,H3=;20p=ef6f5f4R53[A[431=;205;2p=v1H541H31=;205;2p=u%`4,@5?[31=;20p=BA;210p=rg00LRR3P1g0109P0Cxp=Y%20#2#2#2p=ng00P]R0g00Q;R1#ZR5'MR4g00RHR6#ZR7'MR8P4P7P0P5g00SSR9#O#^#C#3#<#5%W1C=%W6C=R6;?61M33R1/M3R:/M3R;P:P3P1P3P3P3%19#R#G#3#Q#{#>g00V6R<#2R=#2R>#2R?#2R@#2RA#2RB#URCC=g00W_RD%U<RE%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#`#>3_C=%F9#<#E#E#5RM#>C=RN;?NROg00XkRPg00XKRQ;?QRR%Z2RS%aBRB#aRT#2#i#S#SRU#URV%09#J#9#3#DRW%19RX#1RY#1RZ#6#6#6R[#h#6R\#J#6#E#N#DR]3V%4IRI,]V%0L#3RL#3R^#O#3R_,gER`%4_Rag00VURb,@VRV%4^R^Cc1]EI%N[#N#N#D%0_#N#N#D5VE1\`aPE%OZPB%>bRZPE%OYRY#0PBPZPE%0XRX#7PBPZPE%0XRX#OPBPZPE%1FR_#7PB%4J#>9_DEPE%3_PB%19#b#Q#9#7#5#>PE%7GPB%4F#>PEPKPB%4H#>RH9_DEPEPYPB%O9#Q#6#E#:#5#>AVCW]1]CIP`Pa1@CbP^Cc%P9#<#E#3#D,@Z%1X#b#3#D'\%P9#<#6#Q#3%b9#G#6#E#8#R#4%99#^#6#3#G#4%<9#^#6#3#G#4%F9#9#D%P9#8#3#6#:%09#J#3#<#6#5%F9#9#R#5RX,@ZPB%>X%P9#8#3#G#C#5,@ZP@%UARA%F9#9#Q#E%F9#<#D%P9#8#3#8#:%F9#<#:#5%F9#<#C#:%F9#<#7#5%P9#8#3#6#3%I9#8#R#3#7%09#J#3#7#7#5RX1@ZX?zH>%C9#C#7#:#:#7%I9#8#9#9#E#5'y%C9#C#7#:#Q#R#4%I9#8#9#<#C#5RH1@ZHPB%U?%I9#8#9#<#7%09#J#3#7#6#5%I9#8#9#:#:%09#J#3#G#9#5R?1@Z?PB%4LRL#>%I9#8#9#:#8%09#J#3#G#G#5%I9#8#:#:#7%49%4\5VA1HbL%W2RL3L7AW3ACf3A3ACf3w3L3A5eM3A3A3AFv3ADu5e^3L3LDBDBDBDBDBDBDBDBDB3L3L3LRM;?MRWg0114Rb#ZRA/MSR\PAPS%Wb9;b<1\V^/rLC=RL;?LR^'KRV'KRb'K1T86POPb1T;NPRPV1TPQPWP^1TSM1T\LCXCXCXCXP4P7P0P5g00YKR01M05g00ZYg011S3dR77d5R4#qAp057C=%o4C==?86P:P3P1P3P3P31Y=Z1YTZC=1Y>ZC=1Y@ZC==?;N%aU#n#S#S#Sg012MRU'm=?PQ%lUg013HRU5?SPAPSg014CRSg015>RAg016;g0176P<DkP2P21sSAg00^WCt,jUC==?\L'K'K'K'Kdo"). Qed.
End VP1.
