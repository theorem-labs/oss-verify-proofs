(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23OpenFail_defs O23Open_defs O23Oom_defs O23DirRead_defs O23ReadLoop_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Grow_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs6g_sr1tC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K4ELinuxProcessSemantics5Riscv5Instr5aluop07K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4bool00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_r1nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs6cap2_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_r1tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_knMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_sr2C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib3O23<O23Grow_defs4g_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs6g_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs6g_kn3iC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_sr3C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib3O23<O23Grow_defs4g_r3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_knLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_rvlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Grow_defs5g_srLC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23ReadLoop_defs4sr_LC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPSG : list Z := (0x62d64 :: STOPSL)%Z.
Definition runG (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSG scr ss [].

(* [comment removed for export] *)
Definition g_ss1 : sym_state := SS 0x62bb0 sr_F [] kn_ML NXL.
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
  KRange (EVar 51) 0x145000 0x7fffff7f0000 :: KAlign (EVar 51) 16 :: KWr (SA (EVar 51) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 51) 0) 65536 :: g_knM.

(* [comment removed for export] *)
Definition g_r2 := Eval vm_compute in runG (SCR [false; false] [] []) (SS 0x62bc4 g_srM [] g_knOK 73).
Definition g_sr2 : list expr := Eval vm_compute in s_regs (fst (fst g_r2)).
Definition g_kn2 : list kentry := Eval vm_compute in kn_after g_r2 g_knOK.

(* [comment removed for export] *)
Definition g_sr3i : list expr := Eval vm_compute in sr_after_call_j g_sr2 KEPT_MC 73.
Definition g_kn3i : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x113000 g_kn2.
Definition g_r3 := Eval vm_compute in runG scr0 (SS 0x62be0 g_sr3i [] g_kn3i 105).
Definition g_sr3 : list expr := Eval vm_compute in s_regs (fst (fst g_r3)).
Definition g_kn3 : list kentry := Eval vm_compute in kn_after g_r3 g_kn3i.

(* [comment removed for export] *)
Definition g_srL : list expr := Eval vm_compute in sr_after_call_j g_sr3 KEPT_AL 105.
Definition g_knL : list kentry := Eval vm_compute in kn_acall g_kn3.
Definition g_rvl : list expr := rvl9 (EVar 51) (EVar 8) cap2_x g_srL.

Section VP1.
Lemma g_itin1 :
  (s_pc (fst (fst g_r1n)), snd (fst g_r1n), s_log (fst (fst g_r1n)))
    = (0xfa4b4%Z, [SCBr false BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ (nth 1 g_sr1 (ELit 0), nth 10 g_sr1 (ELit 0), nth 2 g_sr1 (ELit 0), nth 4 g_sr1 (ELit 0))
     = (ELit 0x62bc4, cap2_x, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x123d20)
  /\ cap2_x = EMd M_MUL (ELit 2) (EVar 8)
  /\ (s_pc (fst (fst g_r1t)), snd (fst g_r1t), s_log (fst (fst g_r1t)))
    = (0x62d64%Z, [SCBr true BC_NE (EAlu ALU_SRL (EVar 8) (ELit 26)) (ELit 0)], [])
  /\ kn_after g_r1t kn_ML = kn_ML
  /\ (nth 2 g_sr1t (ELit 0), nth 3 g_sr1t (ELit 0), nth 4 g_sr1t (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x123d20)
  /\ kn_vars_lt 41 g_kn1 = true /\ kn_acall g_kn1 = g_knM.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Grow_defs ()) ["VP1"] "p;1p;2p;3p;4g0000j1gTg000Pj2TTg0010j18Tg001Oj1VTg002Xj11Tg003=j10Tg003bj3[Tg004kj1PTg0064j4pTg007Aj1cTg007aj3>Tg008Aj4<Tg008aj34Tg009;j3sTg00:Dj1`Tg00:bj15Tg00;@j2jTg00<Kj3]Tg00=Vj2iTg00>aj2NTg00?kj4{Tg00A6j3yTg00BAj2dTg00CLj26Tg00Cgj2FTg00DAj4LTg00D\j3YTg00E9j1mTg00F@j3lTg00F]j1kTg00Gej2vTg00Hgj2uTg00Inj1tTg00Jkj3oTg00L6j4nTf0R0#1#1#1#1p=3%00#1#0#0p=;%10#0#0#1p=7%00#1p=f%10#0#1#0p=:%00#5p=b%80#8p=_%10#0p=U%50#Pp=H%00#0#1#0p=D%10#0#1#1p=M%10#1#0#0p=Ig00LRR1P1f1R2P0C<p=Wf2R3P1P2P0C<p=C%00#0#1#0#0#0#1#1#1p==%00#0#0#5p=2%00#0#0#1p=J%00#1#1#0p=^%00#0#0#0p=?%00#0#0#0#0#0#0#0p=@%00#0p=O%`0,N2p=rf3R4%`3'N?o20p=B%10#0#0#0p=A%10#1p=q%00#1#1#1p=\%00#1#0#0#0p=h%10#1#1#0p=S%00#0#1#1p=R%00#1#0#0#0#0#1#1#1p=E1N43?o20p=Z%00#0#1p=z%52/d0p=e%10#0#0#0#0#1#1#1p=xg00M[R5A>5207>3p=G1d32=>50p=9A>520p=wf4A>5209>539>545>5p=QP1P2g00NfP0Cnp=XP1P2g00OaP0Cnp=a%80#8#8#8p=Kg00P]R0g00Q;R2#gR4'TR3g00RHR6#gR7'TR8P3P7P0P4g00SSR9#3#;#7#f#:#bg00T8g00TXR:g00UJg00V6R;#8R<#8R=#8R>#8R?#8R@#8RA#_RB#VRC%19RD#0RE#URF#H3[RGg00VURH#PRICp%c2RJ5>2C<%c6R6C<RK;4K1T11RL/T1RM/T1RN%U9#D#M#I#;#HROg00W3%09RP#HRQ;sCRC'Wg00W_RR%V;R;%0PRS#0RT#0RU#0RV#0RW#0RX#`#P3[RY5CL%=9#:#;#2RZ#PR[5CMR\;4\R]A41CCR^P3P7P0P4%19#J#^#M#D#bg00XKR_P:PGPICp=>2JC<P6C<R6=486RJ%g5R2%5URG,j;R:%1DRD#1R`#3#3#3Ra#?#@#@#@#2%0X#?RX#?Rb#0#O#?Rc#0#?#@#@#25];Rd1r;cRe%5cRc'iRfP;%0`#OPBPICBR`P;%0D#ORD#0PBPICBRgP;%OFPBPICBRFP;%?EPBPICBREP;%1PRP#APB%HV9[R;CBRVP;%?PPB%U9#D#M#J#I#HCBRPP;%ASPBPQCBRQP;PWPB%HTRW9[R;CBRRP;PDPB%19#q#7#:#\#I#HCBRD%VARA%h9#:#@#2R;%qa#3Ra#U#3#S#?#@#23]RS1jAGRG1NAHRA%5bRb'iPePcPAPbC{%UT#^#@#2,NI%U9#;#@#2'i%09#D#\#;#D#2%J9#R#:#J#J#5%O9#;#S#7#f#7#5%O9#A#S#7#f#7#5%=9#A#:#2%=9#:#\#2%E9#:#7#2PI%=9#A#M#2RTPB%PTCZPI%=9#A#3#2P?%V@R@CZ%z9#J#S#;#D#b%=9#7#:#2%=9#7#M#2%=9#7#S#2%=9#7#3#2%=9#:#D#2%=9#:#^#2%E9#:#I#2%E9#3#D#2RT1NIT?yW=%;9#R#3#7#A%E9#3#;#2'e%;9#R#3#M#J#5%E9#3#\#2RWPIPWPB%V>CZ%;9#R#3#I#?%E9#3#7#2'e%E9#3#M#2%E9#3#I#2RWPIPWPB%5XRX#PCZ%;9#R#3#S#A%h9#A#?#R#2'e%h9#x#I#2%59%5a5]@1dHX%c53G79;3G393G393G3959Z3939393G39393959b3GRb'w3GDQDQDQRZ;4ZR;%AU#@#H,WY=CL[RU=4MUR5g00XkRX?4__RHP:PdPfP`PgPFPEPVPPPQPRPDAGSGbDQDQDQRb=42bRG'6RS'6RD'6RR'6RQ'6RP'61F8KP]PP1FN\P^PQ1F1CPJPR1F86P;PD1F2ZP5PS1FMUPHPG1FX_1F2bCLCLCLCLCLCLCLP3P7P0P4g00YKRb1Tb4RGg00ZYRHg00[e3YRS7Y4R5#mAlb4SC<%k5C<=48K1X<I%_BRB/XI'W1X=I5CL1X?I5CMP1P1POg00\`ROC<=CLY=CM[54NA41OCP3P7P0P4g00]\R09YGHRH9Yb4RG#mAlb4HC<%kGC<=486g00^WR6,v0=4261a=I1a>I'W1a?I5CL=4MU%8B#_#K#K#K#K#K#K#Kg00_VRB'u=4X_%tBg00`Q542'6'6'6'6'6'6'6do"). Qed.

Lemma g_itin2 :
  (s_pc (fst (fst g_r2)), snd (fst g_r2), s_log (fst (fst g_r2))) = (0x109cb0%Z, [SCBr false BC_EQ (EVar 8) (ELit 0)], [])
  /\ (nth 1 g_sr2 (ELit 0), nth 10 g_sr2 (ELit 0), nth 11 g_sr2 (ELit 0), nth 12 g_sr2 (ELit 0))
     = (ELit 0x62be0, EVar 51, EVar 6, EVar 8)
  /\ sr_vars_lt 73 g_sr2 = true /\ kn_vars_lt 73 g_kn2 = true
  /\ sr_after_call_j g_sr2 KEPT_MC 73 = g_sr3i /\ kn_call [] 0 0 IHI 0x113000 g_kn2 = g_kn3i /\ kn_vars_lt 73 g_kn3i = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23Grow_defs ()) ["VP1"] "p;1p;2p;4p;3p;6g0000j1`Tg000Pj2PTg003=j10Tg0010j11Tg001Oj1?Tg004kj1ITg0064j4oTg007Aj1\Tg007aj36Tg008Aj4ATg008aj3BTg00:Dj1dTg003bj3cTg002Xj12Tg009;j3pTg00:bj19Tg00<Kj3aTg00;@j2gTg00>aj2@Tg00?kj4mTg00=Vj2lTg00A6j3|Tg00BAj2OTg00CLj2>Tg00Cgj2TTg00DAj4QTg00D\j3hTg00E9j1vTg00F@j3uTg00F]j1tTg00aLj2sTg00Hgj2iTg00bSj3rTg00caj6wTg00Jkj3_Tg00L6j4qTf0R0#0#0#0#2p=7%00#0#2#2p=[%20#0#0#2p=;%00#2#2#0p=e%00#0#0#9p=3%10#1p=V%20#0p=Y%00#0#2#0p=M%20#0#2#2p=X%20#2#2#0p=<%00#0#0#0p=:%90#Ip=H%10#1#1#1p=W%10#1#1#1#1#1#1#1p=R%20#0#0#0p==%00#0#0#0#0#0#0#0p=C%00#2#0#0p=8%00#2#2#2p=5%20#0#2#0p=F%00#0p=U%00#2p=bg00LRR1f1R2#?;60p=]f2R3#?%?2=610561p=NA61209613p=J%00#2#0#0#0p=G%20#2#2#2p=4%20#2p=n%d0,@2p=}%20#2#0#0p=L%00#0#2p=Z%00#2#0p=S%92/O0p={g00M[R4A6420763p=K%03#9/O2=640p=Df3R5?_32=640p=k1O32=640p=z%02#9,O3=640p=jf6f5f4R63_A_532=640564p=y1O651O32=640564p=x%d5,@6?_32=640p=EP1P2g00dfR2P0Cqp=^g00XkR3g00XKR67B0p=fg00P]R0g00Q;R5#`R7'PR8g00RHR9#`R:'PR;P8P:P0P7g00SSR<#0#7#[#;#e#3g00T8g00eag00V6R=#1R>#1R?#1R@#1RA#1RB#1RC#VRD#?REg00VURF#IRGCo%\5565CA%\9CAR9;B91P11R5/P1RH/P1RIPHP1P5P1P1P1%Y<#M#X#<#:#HRJ%VDRK#1RL#1RM#1#W#R#RRN#1RO#1RP#1RQ#1#V#W#RRR#?RSCA%?CRCCAPECART;BTRUAB366RV%`1RW%VR#W#R#RRRg00W_RX%?=R=%0<RY#0RZ#0R[#0R\#0R]#0R^#0R_#d#I3c%=\#C#H%0<#8#5#F#8#3R`#I%1R#WRa%1aRa%1aRa%HYRb%WaRa#?%1aRa%1aRa%1aRa%1aRa%1aRa%1aRa%2<Rc#Hg00W3?pbE%U<#8#<#;#b#;#9Rd#I%?N%1a#V#RRa%1aRa%1aRa%1a%\1']3N5NQ9NOP5JC3J5JE,]?3N3N3N5JS7JS']3N3J5JJ']RJ;BJRE%`4RP%G<#F#C#3RO%2cRQ#2Ra#4#4#4RN#n#4Re#Y#4#<#:#C#3Rf5aS%9\R\,gS%0_#:R_#:Rg#0#U#:Rh,}=Ri%9hRj1@SF%9gRgCm1g=\%:N#C#C#C#3%0h#:#C#C#35a=1lijP=%0a#UPDPGP=%0Q#URQ#0PDPGP=%0cRc#=PDPGP=%:cPDPGP=%2YRY#=PD%H]9cX=P=%:YPD%Y<#M#X#7#L#HP=%=ZPDPbP=P^PD%H[R^9cX=P=PQPD%2<#n#;#F#5#L#HAaCOf1gC\PiPj1@CFPgCm%Y[#e#C#3R[,@G%Y<#8#C#3'l%0<#M#5#b#:#=%7<#[#F#7#7#9Pd%U<#=#<#;#b#;#9%0<#8#5#=#F#3%Z<#7#<#;#L%G<#5#F#;#3%0<#8#5#=#X#3Rd,@GPD%Id%0<#8#5#=#4#3,@GPA%?BRB%Z<#7#<#8#M%0<#8#5#;#F#3%Z<#7#<#e#L%0<#8#5#;#<#3%Z<#7#<#5#L%0<#8#5#F#M#3%Z<#7#<#;#=%S<#7#<#X#:%G<#5#4#M#3RA1@GA?|^?%8<#[#4#;#=%G<#5#4#8#3'{%8<#[#4#X#7#9%G<#5#4#5#3R^1@G^PD%?@%S<#7#4#<#:%G<#5#4#;#3%S<#7#4#<#L%G<#5#4#L#3R@1@G@PD%9_R_#I%S<#7#4#4#8%G<#=#:#[#3%S<#M#7#4#:%9<%9e5aB1OF_%\43K7DO3DCk3D3DCk3z3K3D5j`3D3D3DFy3DDx5jg3K3KDEDEDEDEDEDEDEDEDE3K3K3KRg;BgR`/>VRO'>R4,>VR_'>RB'>1T;9PUPB1TITPVP_1T36R6PVP4P6PEPO1TWJP`PV1TPgP6CQCQCQCQCQCQP8P:P0P7g00YKR:1P:7g00ZYg00fS3hR87h7R6#vAu:78CA%t6CA=B;9PHP1P5P1P1P11^>G1^KGCA1^LGCA1^MGCA=BIT1sR2#fg00gMRT,iR#fg00hH=r2Rg00iI5BW1P00#\PFPFg00jEP[PTEwg00kBRT5BP1iRT#f'>'>'>'>'>'>do"). Qed.

Lemma g_itin3 :
  (s_pc (fst (fst g_r3)), snd (fst g_r3), s_log (fst (fst g_r3))) = (0xfa374%Z, [], [])
  /\ (nth 1 g_sr3 (ELit 0), nth 10 g_sr3 (ELit 0), nth 2 g_sr3 (ELit 0), nth 4 g_sr3 (ELit 0))
     = (ELit 0x62be8, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x123d20)
  /\ kn_vars_lt 105 g_kn3 = true /\ kn_acall g_kn3 = g_knL
  /\ (sr_mismatch g_rvl idb g_srL sr_L 0, kn_missing g_knL (map (kmap g_rvl idb) kn_ML)) = ([0%nat], [KWr (SA (EVar 51) 0) 65536]).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Grow_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j1[Tg000Pj2HTg007Aj1VTg008Aj4<Tg008aj3@Tg002Xj11Tg004kj1=Tg0010j12Tg001Oj1OTg003=j10Tg00:Dj1aTg003bj3_Tg00<Kj3UTg00:bj15Tg00;@j2]Tg00>aj2BTg00?kj4dTg00=Vj2\Tg00A6j3zTg00BAj2KTg007aj3;Tg00CLj2JTg00Cgj2QTg00DAj4WTg00D\j3eTg00E9j1qTg00F@j3pTg00F]j1oTg00Hgj2mTg00Inj1lTg00l>j5kTg00mKj2rTg00nQj4sTg00nmj2tTg00Jkj3YTg00L6j4iTf0R0#1#1#1#1p=4%00#1#0#0p=9%00#1#1#0p=c%10#1p=R%10#0#1#0p=G%00#5p=b%00#0#0#1p=7%00#1p=A%00#0#0#5p=3%00#1#1#1p=6%20#2p=`%20#2#2#2#2#2#2#2p=j%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=S%00#1#0#0#0p=C%00#0#0#0#0#0#0#0p=D%10#0p=^%10#1#1#0p=8%00#0#0#0p=:%00#0p=Pf1R1%a0'Bp=h%10#0#0#0p=>%00#0#1#1p=N%00#0#1#0p=M%10#0#0#1p=?%00#0#1p=L%10#1#0#0p=T%51/K0p=y%00#1#0p=Zg00M[R2f2R3A;2103;p=I%03#5/K1=;20p=Ef3R4?Y31=;20p=g1K31=;20p=x%01#5,K3=;20p=ff6f5f4R53YAY431=;205;2p=w1K541K31=;205;2p=v%a4,B5?Y31=;20p=FA;210p=ug00LRR3P1g0109P0Cip=X%20#2#2#2p=ng00P]R0g00Q;R1#[R5'HR4g00RHR6#[R7'HR8P4P7P0P5g00SSR9#4#9#c#R#G#b%V1C<%V6C<R6;@61H33R1/H3R:/H3R;P:P3P1P3P3P3%19#7#A#A#4#A#3#=g00V6R<#2R=#2R>#2R?#2R@#2RA#2RB#ORCC<g00W_RD%O<RE%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#a#=3_C<%09#9#6#G#9#3RM#=C<RN;@NROg00XkRPg00XKRQ;@QRR%[2RS%`BRB#`RT#2#j#S#SRU#ORV%C9#G#D#3RW%19RX#1RY#1RZ#4#4#4R[#R#4R\#^#4#8#:#D#3R]3U%5IRI,]V%0L#:RL#:R^#0#P#:R_,hER`%5_Rag00VURb,BVRV%5^R^Cd1]EI%:[#D#D#D#3%0_#:#D#D#35UE1\`aPE%0Z#PPB%=bRZPE%0Y#PRY#0PBPZPE%0XRX#>PBPZPE%:XPBPZPE%1FRX#>PB%5J#=9_DEPE%:XPB%19#7#A#A#>#8#b#=PE%>GPB%5F#=PEPKPB%5H#=RK9_DEPEPYPB%49#N#A#N#8#b#=AUCW]1]CIP`Pa1BCbP^Cd%^H#c#D#3,BZ%^9#9#D#3'\%09#M#6#A#:#>%79#N#G#7#7#5%P9#9#8#?#A#?#5%P9#>#8#?#A#?#5%09#9#6#>#G#3%L9#7#8#?#T%C9#6#G#?#3%L9#7#8#M#R#3RH,BZPB%=H%09#9#6#>#4#3,BZP@%OARA%L9#7#8#9#M%09#9#6#?#G#3%L9#7#8#c#T%09#9#6#?#8#3%L9#7#8#6#T%09#9#6#G#M#3%L9#7#8#?#>%C9#6#G#R#:%C9#6#4#M#3RH1BZH?zK>%99#N#4#?#>%C9#6#4#9#3'y%A9#:#4#8#R#7#5%C9#6#4#6#3RK1BZKPB%O?%Z9#7#4#8#:%C9#6#4#?#3%Z9#7#4#8#T%C9#6#4#T#3R?1BZ?PB%5LRL#=%Z9#7#4#4#9%C9#>#:#N#3%Z9#M#7#4#:%59%5\5UA1KbL%V2RL3I7EW3ECg3E3ECg3x3I3E5fM3E3E3EFw3EDv5f^3I3IDFDFDFDFDFDFDFDFDF3I3I3IRM;@MRWg0114Rb#[RA/HSR\PAPS%Vb9;b<1\V^/uLC<RL;@LR^'JRV'JRb'J1Q86POPb1Q;NPRPV1QPQPWP^1QSM1Q\LCWCWCWCWP4P7P0P5g00YKR01H05g00ZYg011S3eR77e5R4#qAp057C<%o4C<=@86P:P3P1P3P3P31X=Z1XTZC<1X>ZC<1X@ZC<=@;N%`U#n#S#S#Sg012MRU'm=@PQ%lUg013HRU5@SPAPSg014CRSg015>RAg016;g0176P<DkP2P21rSAg00^WCs,tUC<=@\L'J'J'J'Jdo"). Qed.
End VP1.
