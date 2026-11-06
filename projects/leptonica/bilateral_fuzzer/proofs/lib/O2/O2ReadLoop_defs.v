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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall O2OpenFail_defs O2Open_defs O2Oom_defs O2DirRead_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2ReadLoop_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs3e_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5e_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4e_srC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4e_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<LibKnowFrame8kn_frameC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srAnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rAnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6want_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rAtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srAtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4l_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_srCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rC2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5h_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srC2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_HC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_knC2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_srBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4l_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_knD0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rDnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_rDtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5l_knDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5d_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srDnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs5f_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs6l_srDtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2ReadLoop_defs4sr_FC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPSL : list Z := (0x176e4 :: 0x17714 :: 0x176ac :: STOPS3)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSL scr ss [].
Definition NXL : nat := 41.
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_L : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x49840; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; ELit 3; EVar 8; ELit 0x39739; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x49840; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_F : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x49840; J 5; J 6; J 7;
   ELit 2; J 9; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 8; ELit 3; EVar 8; ELit 0x39739; EVar 6;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_ML : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-8388608)) 8388608;
   (* [comment removed for export] *)
   KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-88)) 8 (spx 32); KWord (SA (EVar 0) (-80)) 8 (ELit 0x17618);
   KWord (SA (EVar 0) (-72)) 8 (ELit 2); KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-56)) 8 (ELit 0x2efd8);
   (* [comment removed for export] *)
   KRange (EVar 6) 0x6b000 0x7fffff7f0000; KAlign (EVar 6) 16; KWr (SA (EVar 6) 0) 65536;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 6) 0) 65536;
   (* [comment removed for export] *)
   KWr (SA (ELit 0) 0x39000) 204800;
   KImg 0x10000 0x396f0; KImg 0x396f1 0x39739; KImg 0x49739 0x49770; KImg 0x49858 0x69868;
   KWord (SA (ELit 0) 0x49778) 8 (ELit 0x49778); KWord (SA (ELit 0) 0x49798) 4 (EVar 5);
   KImg 0x497a4 0x497f0; KImg 0x497f8 0x49810; KImg 0x49818 0x49830; KImg 0x49840 0x49850; KImg 0x69880 0x69aa8;
   KBlob (SA (ELit 0) 0x69aa8) (ELit 8) 2; KImg 0x69ab0 0x69ab8; KImg 0x69ac9 0x69ad0;
   KWord (SA (ELit 0) 0x69ad0) 8 (EVar 3); KImg 0x69ad8 0x69ae0; KImg 0x69af0 0x69af8;
   KWord (SA (ELit 0) 0x69af8) 8 (ELit 4096); KImg 0x69b00 0x69b30; KImg 0x69ee8 0x6b000;
   KRange (EVar 5) 1 4194303; KImg 0 0x1000].

(* [comment removed for export] *)
Definition rvl9 (ebuf elen ecap : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; ebuf; elen; ecap] ++ (ELit 0 :: tl sr).
Definition idb (k : nat) : nat := k.

(* [comment removed for export] *)
Definition e_r := Eval vm_compute in runL (SCR [false] [] []) d_ssR0.      (* [comment removed for export] *)
Definition e_sr : list expr := Eval vm_compute in s_regs (fst (fst e_r)).
Definition e_kn : list kentry := Eval vm_compute in kn_after e_r ok_kn.
Definition e_rvl : list expr := rvl9 (EVar 48) (ELit 0) (ELit 65536) e_sr.

(* [comment removed for export] *)
Definition l_ssA : sym_state := SS 0x176e4 sr_L [] kn_ML NXL.
Definition l_rAn := Eval vm_compute in runL (SCR [false] [] []) l_ssA.   (* [comment removed for export] *)
Definition l_rAt := Eval vm_compute in runL (SCR [true] [] []) l_ssA.    (* [comment removed for export] *)
Definition l_srAn : list expr := Eval vm_compute in s_regs (fst (fst l_rAn)).
Definition l_srAt : list expr := Eval vm_compute in s_regs (fst (fst l_rAt)).
Definition l_knA : list kentry := Eval vm_compute in kn_after l_rAn kn_ML.
(* [comment removed for export] *)
Definition l_srR (e : expr) : list expr := sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) e.
Definition l_knR : list kentry := Eval vm_compute in kn_frame l_knA (ELit 0) 0x39739 65536.

(* [comment removed for export] *)
Definition l_rC := Eval vm_compute in runL scr0 (SS 0x37344 (l_srR (ELit 0)) [] l_knR 42).
Definition l_srC : list expr := Eval vm_compute in s_regs (fst (fst l_rC)).
Definition l_knC : list kentry := Eval vm_compute in kn_after l_rC l_knR.
Definition l_rC2 := Eval vm_compute in runL scr0 (SS 0x37344 (sr_upd l_srC (ridx 10) (ELit 0)) [] l_knC 42).
Definition l_srC2 : list expr := Eval vm_compute in s_regs (fst (fst l_rC2)).
Definition l_knC2 : list kentry := Eval vm_compute in kn_after l_rC2 l_knC.
Definition h_rvl : list expr := rvl9 (EVar 6) (EVar 7) (EVar 8) l_srC2.

(* [comment removed for export] *)
Definition l_knRB : list kentry := KRange (EVar 42) 1 65536 :: l_knR.
Definition l_rB := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x37344 (l_srR (EVar 42)) [] l_knRB 43).
Definition l_srB : list expr := Eval vm_compute in s_regs (fst (fst l_rB)).
Definition l_knB : list kentry := Eval vm_compute in kn_after l_rB l_knRB.

(* [comment removed for export] *)
Definition l_srD0 : list expr := Eval vm_compute in sr_after_call_j l_srB KEPT_MC 43.
Definition l_knD0 : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x39000 l_knB.
Definition l_rDn := Eval vm_compute in runL (SCR [false] [] []) (SS 0x17698 l_srD0 [] l_knD0 75).  (* [comment removed for export] *)
Definition l_rDt := Eval vm_compute in runL (SCR [true] [] []) (SS 0x17698 l_srD0 [] l_knD0 75).   (* [comment removed for export] *)
Definition l_srDn : list expr := Eval vm_compute in s_regs (fst (fst l_rDn)).
Definition l_srDt : list expr := Eval vm_compute in s_regs (fst (fst l_rDt)).
Definition l_knD : list kentry := Eval vm_compute in kn_after l_rDn l_knD0.
Definition d_rvl : list expr := rvl9 (EVar 6) (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8) l_srDn.
Definition f_rvl : list expr := rvl9 (EVar 6) (EVar 8) (EVar 8) l_srDt.

(* [comment removed for export] *)
Definition want_x : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 7)) (EVar 8).

Section VP1.
(* [comment removed for export] *)
Lemma e_itin :
  (s_pc (fst (fst e_r)), snd (fst e_r), s_log (fst (fst e_r))) = (0x176e4%Z, [], [])
  /\ (sr_mismatch e_rvl idb e_sr sr_L 0, kn_missing e_kn (map (kmap e_rvl idb) kn_ML)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j14Tg000Pj26Tg0010j11Tg001Uj10Tg002:j1CTg002Xj15Tg0038j42Tg003Xj33Tg0042j3;Tg004Rj28Tg004lj49Tg005Gj37Tg005dj1:Tg006kj3BTg007Hj1ATg008Pj5@Tg009]j2=Tg00:cj4>Tg00;?j2?Tg00<Kj2<Tg00<fR0g00=DR1#4R2'6R3g00>QR4#4R5'6R6P3P5P0P2g00?\#1#0#0#0#1#0#0#1#0#0#0#1#1#0#1#1#C%51C2%54C2R4;34g00@AR1#4R7g00@`R8#4R9'6R:P7P9g00AkR;%515;1%58C2R1;31186418:1C9P3P5P0P2g00BJR01602g00CXg00Dd37R5772R3#:AB025C2%A3C2=364P7P9g00E_R9g00F\R7g00GWg00HSP;D@g00IOP8P81=97g00JKC>'?C2=3:1'<do"). Qed.

Lemma l_itinA :
  (s_pc (fst (fst l_rAn)), snd (fst l_rAn), log_win_b 0 (s_log (fst (fst l_rAn))))
    = (0x37340%Z, [SCBr false BC_LTU want_x (ELit 65536)], true)
  /\ (s_pc (fst (fst l_rAt)), snd (fst l_rAt), log_win_b 0 (s_log (fst (fst l_rAt))))
    = (0x37340%Z, [SCBr true BC_LTU want_x (ELit 65536)], true)
  /\ kn_after l_rAt kn_ML = l_knA
  /\ (nth 17 l_srAn (ELit 0), nth 10 l_srAn (ELit 0), nth 11 l_srAn (ELit 0), nth 12 l_srAn (ELit 0))
     = (ELit 63, ELit 3, ELit 0x39739, ELit 65536)
  /\ nth 12 l_srAt (ELit 0) = want_x
  /\ sr_upd l_srAt (ridx 12) (EVar 41) = sr_upd l_srAn (ridx 12) (EVar 41)
  /\ sr_vars_lt 41 l_srAn = true /\ sr_vars_lt 41 l_srAt = true /\ kn_vars_lt 41 l_knA = true
  /\ kn_frame l_knA (ELit 0) 0x39739 65536 = l_knR
  /\ sr_vars_lt 42 (sr_upd l_srAn (ridx 12) (EVar 41)) = true /\ kn_vars_lt 42 l_knR = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop_defs ()) ["VP1"] "p&0p;1p;2p;3p;4g0000j1lTg000Pj2WTg00KHj1]Tg00Kfj1FTg00Loj12Tg00MNj1>Tg00NWj3xTg00O`j3cTg0010j10Tg002:j15Tg00Pij4aTg002Xj1jTg0042j34Tg003Xj37Tg00R6j2pTg001Uj11Tg00SAj3fTg00TLj2eTg00UWj2DTg00Vak409Tg00Wlk307Tg00Y7j2LTg0038j4ATg00<Kj29Tg004Rj2QTg004lj4hTg005Gj3_Tg005dj1tTg006kj3sTg007Hj1rTg00ZBj2mTg00[Ik201Tg00\Ij4qTg00\ek100Tg00]Cj2~Tg00]fj3}Tg00^Ij1|Tg00_Pj3vTg00`Yj2iTg00a`j2oTg00bgj4{Tg00d2j3\Tf0R0#1#0p=R%10#1#1#0p=I%00#1#1#0p=T%10#0#0#0p=;%00#0#0#5p=3%20#2p=B%00#0p=V%00#0#0#0p=6g00<fR1f2R2f1R3P0CAp=UP3g00e=R4P0g00e]R5CAp=`%00#1#1#1p=H%00#0#0#0#0#0#0#0p=?%50#Fp=@%10#1p=g%10#1#1#1p==%]0,D3p=z%00#]p=nf3R6/D2?\30p=y%00#1p=d%10#1#0#1p=N%10#0#1p=J%00#1#0#0p=:%10#0#0#1p=M%50,L3p>08%00#1#0#1p=S%10#0#1#1p=b%10#1#0#0p=<%00#0#1#1p=8%00#0#1p=P%00#0#1#0p=K%10#0#1#0p=k%53/L0p>06g00@`R7A4730742p=O%02#5/L3=470p=EA\623=470p=w1L23=470p>05%03#5,L2=470p>04f6R8f5R9f4R:3\A\623=470547p>031L:61L23=470547p>02%]6,D:?\23=470p=Gg00f=R;%>3;40p=u%>2%>3=4;054;p=YA4;3094;2p=CP8P9P:P6P2P3P0ChChp=XP;P3g00gFR6P0Cqp=^A7405p=Z1930,92p=[g00=DR2#lR3,W1R1/W4R0g00?\R:#R#I#T#;#3R9g00hDR8g00hdR<g00iVR=g00jB%]:#Fg00AkR>#BR?#2R@#2RA#2RB#2RC#2RD#>RE3x%2DRD#>RF3cRG%0:RH#0RI#0RJ#0RK#0RL#0RM#V#6RN#6RO#5RP#FRQCa%j2RR5425U3,`1RS;7SP5P<PGPQCa=42R9U39,`1RT=70TRU%l7RV%>>RW%;JPD%H:#H#?#@%5KRX,pW%1:RY#1RZ#1R[#gR\#g#=#=R]#6#?#?#?#3%0O#V#6RO#0#6#?#?#35fW1zWOR^%5ORO'ePW%V[#nPDg00jnR[#FR_CyPW%VZRZ#0R`#0PDP_PW%0YRa#;PDP_PW%0aRa#0#VPDP_PW%1HRb#;PD%@L9c=WPW%6bPD%d:#N#;#d#;#@PW%;IRIPD%@HRHPWPMPD%@JRJ9c=WPWP`PD%0:#I#=#N#;#@%>CRC%J:#T#?#3R`%g]#=R]#R#=#I#6#?#33f1pCX1DC[RX/ePP^POPXPPH09%RZ#?#3,D_%R:#:#?#3'e%1:#M#T#=#6-08P%1:#R#S#b#<#d#5%1:#M#H#8#M#5RZ%V:#M#H#8#M#5%P:#K#I#I#3%0:#:#<#K#<%J:#8#6#N#3%P:#K#I#=#3RX,D_PD%FX%P:#K#=#8#3,D_PA%>BRB%0:#:#b#N#K%P:#K#=#I#3%0:#:#b#=#<%P:#8#6#K#3%0:#:#<#6#<%P:#8#6#T#3%P:#8#6#;#3RA%0:#:#<#K#;%1:#:#<#:#6%J:#8#S#S#3RX1D_X@07J?%R:#M#k#b#6%J:#8#S#H#3+06%R:#M#k#<#M#5%J:#8#S#k#3RJ1D_JPD%>@%1:#:#N#T#<%J:#8#S#<#3%1:#:#N#H#;%J:#8#S#=#3R@1D_@PD%5NRN#F%1:#:#N#;#6%J:#8#T#T#3%1:#:#=#H#:%5:%5]5fB1L[N%j73O7E`3ECw3E3ECw4053O3E4043E3E3EK033EI023O3O3ODGDGDGDGDGDGDGDG3O3ODGR`;7`R71W;;RN/W;R[/W;RBP[P;PNP;P;P;%@\R\%@YRYCA%FZR]CAPQCAR@;7@RJA7;GGRX%l;RO%1:#H#8#I#<#@%nI#F9c=W%;K#?#@%FA%BDRD#2RA#2RK#BRW#>%2WRW%2WRW%2WRW#2#B#B#B#B#B#B#BR=#2RI#2R:#2R^#2RM#2RL#2Rc#2Rd#2Re#2Rf#>Rg%j;,ue9Ycd9YML9Y:^9Y=I9CF]9CEY,u?9C_\9C__7C_9CY]9CHC3Y3C3C5C_RC;7CRHA7455R]19]]RY,97R\,9]R?,9]RE'9RF'9RI'9R='9R^'9R:'91Q0SPUP:1Q0TP7P^1QV`R`PJP=1QB@PXPI1Q;GPHPF1QOCP]PE1Q45REP]P?PEP]P\PEP7PYP`P]P]PEPEChFXFXFXFXFXP1P4g00BJRE1WE3R]g00CXR`g00kL3_RY7_3R7#tAsE3Y5U3%r7,m>CAP8P<g00lIR8PQCa=42R9U39,`1570P1P4g00mGR49_]`R`9_E3R]#tAsE3`5U3%r],m>CAP5P<P8PQCa=42R9U39,`1570g00JK-014g00nDR457VP[P;PNP;P;P;1^W_1^D_CA1^A_CA1^K_CA=7B@P;PKg00oARKP_Cq=7;8&00bRb%5aRag010?1~bad3}#|Ra=vKgAv6agRa57O1if6#Z1ifK#Z1of4#ZP4P_PZPPC{g010[RP57V%2fRf/ia#Z1ofP#Z'93[3[3[3[3[do"). Qed.

Lemma l_itinC :
  (s_pc (fst (fst l_rC)), snd (fst l_rC), log_win_b 0 (s_log (fst (fst l_rC))), nth 17 l_srC (ELit 0), nth 10 l_srC (ELit 0))
    = (0x37340%Z, [], true, ELit 57, ELit 3)
  /\ (s_pc (fst (fst l_rC2)), snd (fst l_rC2), s_log (fst (fst l_rC2))) = (0x17714%Z, [], [])
  /\ (sr_mismatch h_rvl idb l_srC2 sr_H 0, kn_missing l_knC2 (map (kmap h_rvl idb) kn_ML)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop_defs ()) ["VP1"] "p;1p;2p;3p;4p;5g0000j18Tg000Pj23Tg001Uj10Tg002:j1;Tg002Xj1<Tg00Kfj1>Tg003Xj35Tg0038j47Tg00<Kj2=Tg004Rj2@Tg004lj4ETg005Gj39Tg005dj1DTg006kj3CTg007Hj1BTg00ZBj2KTg00Loj1?Tg00\Ij4ATg008Pj5JTg009]j2ITg00:cj4HTg00;?j2GTg0010j1:Tf0R0#:#0p=1%00#:p=F%:0#:p=6f6f5f4f3f2f1C7P0C7p=4%?0#?p=2g00<fR0g00=DR1#8R2'3R3g00e=R4'3R5g00f=R6'3R7/36R8P7P6P5P6P3P4P0P2g00?\R9#0#1#0#F#1#0#1#6#6#6#;%<1R1g00e]F4%09R:#F#1#;#>%;:#>F4R:;5:g00>QR;#8R<,33R=P3P<P0P2%19#0#0#1#0#0#6#1#1#6#;P1%<;F4R;;5;R1g00@AR9#8R>g00@`R?#8R@'3RAP>P@%<9%<?C7R9;59RB'=1@8:P1PB1@=;1@A9CECEP7P6P5P6P3P4P0P2g00BJR41342R5g00CXR7g011X39RB792R1#DAC42Bg00AkRB%B1'KF4P6%2B#2#2#2#2R1#?#2#2#2g012TRCg00jn#>RDCAP6P1PCPDCAF4=58:P3P<P0P2g013Q9957R79942R5#DAC427%B5F4=5=;P>P@g014NR@g00F\R>g015Kg016IPBDJg017EP?P?1I@>g00JKCH'GC7=5A9'='=do"). Qed.

Lemma l_itinB :
  (s_pc (fst (fst l_rB)), snd (fst l_rB), log_win_b 0 (s_log (fst (fst l_rB)))) = (0x36a58%Z, [], true)
  /\ (nth 1 l_srB (ELit 0), nth 10 l_srB (ELit 0), nth 11 l_srB (ELit 0), nth 12 l_srB (ELit 0))
     = (ELit 0x17698, EAlu ALU_ADD (EVar 6) (EVar 7), ELit 0x39739, EVar 42)
  /\ sr_vars_lt 43 l_srB = true /\ kn_vars_lt 43 l_knB = true
  /\ sr_after_call_j l_srB KEPT_MC 43 = l_srD0 /\ kn_call [] 0 0 IHI 0x39000 l_knB = l_knD0 /\ kn_vars_lt 43 l_knD0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop_defs ()) ["VP1"] "p;1p;2p;4p;3p;6g0000j1eTg000Pj2RTg002Xj1^Tg0038j4>Tg003Xj3@Tg00Loj12Tg00MNj1BTg00O`j3`Tg001Uj11Tg002:j16Tg00Kfj1MTg0010j10Tg00KHj1]Tg00SAj3[Tg00R6j2gTg00TLj2fTg00UWj2ATg00Vaj4|Tg00Wlj3{Tg00Y7j2PTg00<Kj2<Tg004Rj2ZTg004lj4STg005Gj3kTg005dj1uTg006kj3tTg007Hj1sTg00ZBj2rTg00`Yj2qTg00a`j2jTg018Cj3pTg019Qj6vTg0042j34Tg00d2j3YTg00\Ij4oTf0R0#1#0p=N%10#1#0#1p=J%00#1#0#0p=7%10#0#1#1p=V%00#0#0#6p=3%00#1#1#1p=C%00#1#1#0p=T%10#0#0#1p=F%10#0#0#0p=9%60#Mp=E%00#0#1#1p=8%20#2p=b%20#2#2#2p=?%00#0#0#0#0#0#0#0p==%00#0#1p=L%00#0#0#0p=5g00f=R1f2R2#Bf1R3#B=41034p=GA41309412p=U%B3=410p=\%00#0p=X%00#]p=if3R4/A2?Y30p=h%10#1#1#1p=:%]0,A3p=n%00#1p=d%10#1#1#0p=W%10#0#1p=K%10#1p=}%10#1#0#0p=;%00#1#0#1p=Q%00#0#1#0p=H%10#0#1#0p=c%63/P0p=zg00@`R5A4530742p=O%02#6/P3=450p=DAY423=450p=m1P23=450p=y%03#6,P2=450p=lf6f5f4R63YAY423=450545p=x1P641P23=450545p=w%]4,A6?Y23=450p=IP1P3g01:VR3P0Cop=_g00e=R2g00e]R67@0p=ag00<fR0g00=DR4#eR7'RR8/R2R9P8P2P0P7g00?\R:#N#J#7#V#3%^4C>P6C>R4;@41R11R;/R1R</R1R=P<P1P;P1P1P1%C:#T#F#9#ER>g00iVR?g00AkR@#2RA#2RB#2RC#2RD#2RE#2RF#BRG%2FRF#BRH3`RIC>%1:#F#C#8#F#6RJ#MRKC>%2FRF#bRL#2RM#2RN#2#?#?#?#?#?RO#2RP#2RQ#2RR#b#?RS#BRTC>RU;@URVA@266RW%e1RX%2SRS%B@RY%0:RZ#0R[#0R\#0R]#0R^#0R_#0R`#]#M5`?%9]#=#E%L:#8#5#9#3Ra#M%2S#?Rb%2bRb%2bRb%EZRc%?bRb#B%2bRb%2bRb%2bRb%2bRb%2bRb%2bRb%1:Rd#E%2b#b#?#?Rb%2bRb%2bRb%2b%^13G3G9GQR9GOP9UKT,\F5UH,\B3G3G3G5UI7UG'\3G3U5U>'\R>;@>RI%e5RH%6:RK%0`#5R`#5RP#6RO5[TPY%1\#X#iPF%C:#C#=#ECh%6]R],gY%1dRT#1RR#:#:#:RQ#5#=#=#=#3%0P#X#5RP#0#5#=#=#35[Y1nYPRb%6PRP'fPY%XR#iPFg00jnRR#MReChPY%XTRT#0Rf#0PFPePY%0dRd#9PFPePY%5dPFPePY%1ZRZ#9PF%E^9`?YPY%5ZPF%d:#J#9#d#9#EPY%9[PFPcPYP_PF%E\R\9`?YPYPfPF%0:#W#:#J#9#E%K:#T#=#3Rf%}Q#:RQ#N#:#W#5#=#35[G1gG]PbPP1AGRPOC|%NT#=#3RT,Ae%N:#7#=#3'f%;:#V#C#9%1:#N#Q#V#;#d#6PJ%X:#F#C#8#F#6%L:#H#W#W#3%0:#7#;#H#;%K:#8#5#J#3%L:#H#W#:#3RJ,AePF%MJ%L:#H#:#8#3,AePD%BERE%0:#7#V#J#H%L:#H#:#W#3%0:#7#V#:#;%L:#8#5#H#3%0:#7#;#5#;%L:#8#5#T#3%0:#7#;#H#9%1:#7#;#7#5%K:#8#Q#Q#3RD1AeD?{\B%N:#F#c#V#5%K:#8#Q#C#3'z%N:#F#c#;#F#6%K:#8#Q#c#3R\1Ae\PF%BC%1:#7#J#T#;%K:#8#Q#;#3%1:#7#J#C#9%K:#8#Q#:#3RC1AeCPF%6`R`#M%1:#7#J#9#5%K:#8#T#T#3%1:#7#:#C#7%6Q9[EK1PR`%^53O7Df3DCm3D3DCm3y3O3D5la3D3D3DFx3DDw5lO3O3ODIDIDIDIDIDIDIDI3O3O3ORO;@ORa/<WRf'<R5,<WR`'<RE'<1Z94PVPE1Z=UPWP`1Z26R6PWP5P6PIPf1ZX>PaPW1ZHOP6CSCSCSCSCSCSP8P2P0P7g00BJR21R27g00CXg01;S3kR87k7R6#uAt278C>%s6,r@C>=@94P<P1P;P1P1P11_Ae1_LeC>1_MeC>1_NeC>=@=U1qS3#ag01<ORU,jS#ag01=L=p3Sg01>K5@X1R00#^PRPRg01?IPTPUEvg01@DRU5@H1jSU#a'<'<'<'<'<'<do"). Qed.

Lemma l_itinD :
  (s_pc (fst (fst l_rDn)), snd (fst l_rDn), s_log (fst (fst l_rDn)))
    = (0x176e4%Z, [SCBr false BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ (s_pc (fst (fst l_rDt)), snd (fst l_rDt), s_log (fst (fst l_rDt)))
    = (0x176ac%Z, [SCBr true BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ kn_after l_rDt l_knD0 = l_knD
  /\ (sr_mismatch d_rvl idb l_srDn sr_L 0, kn_missing l_knD (map (kmap d_rvl idb) kn_ML))
     = ([0%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ (sr_mismatch f_rvl idb l_srDt sr_F 0, kn_missing l_knD (map (kmap f_rvl idb) kn_ML))
     = ([0%nat; 19%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ nth 19 l_srDt (ELit 0) = EAlu ALU_ADD (EVar 7) (EVar 42).
Proof.
ltac2:(KReplay.run1 (kr_t_O2ReadLoop_defs ()) ["VP1"] "p;1p;2p;3p;4p;5g0000j1ZTg000Pj2YTg0010j10Tg00Loj17Tg00MNj1JTg00O`j3\Tg00Pij4nTg002Xj1[Tg0042j34Tg0038j4;Tg003Xj39Tg002:j13Tg00SAj3XTg001Uj11Tg00Kfj1ATg00R6j2cTg00TLj2]Tg00UWj2@Tg00Vaj4zTg00Wlj3yTg00Y7j2NTg00<Kj2CTg004Rj2STg004lj4UTg005Gj3WTg005dj1kTg006kj3iTg007Hj1fTg00[Ij2rTg008Pj5hTg009]j2jTg00;?j2lTg00\Ij4qTg00KHj1`Tg00d2j3TTg00:cj4pTf0R0#1#1p=^%10#0#1#1p=G%00#1#1#1p=M%00#0#1#0p=>%00#3p=g%70#7p=_%70#7#7#7p=H%00#1#0#1p=K%00#1#1#0p=B%00#0p=R%00#0#0#0p=5%00#`p=e%10#1#1#0p=E%00#0#0#3p=2f3R1f2R2'@f1R3;T0p=d%10#1#1#1p=<%00#0#0#0#0#0#0#0p=D%`0,@3p=o%10#0#0#0p=Q%10#1#0#0p=8%00#0#1#1p=:%00#1p=b%10#1#0#1p=L%10#0#1p=O%10#0p==%00#1#0#0p=6%10#0#0#1p=V%00#0#1p=P%33/N0p=xg00@`R4A4430742p=I%02#3/N3=440p=?AT123=440p=m1N23=440p=wf6f5f4R53TAT123=440544p=v1N511N23=440544p=u%03#3,N2=440p=t%`1,@5?T23=440p=FA4430p=sP4P4P0g00JKCpp=ag00<fR0g00=DR3#ZR2'YR5g00>QR1#ZR6'YR7P5P6P0P2g00?\R8#0#^#G#M#>#gg00hDg01ABR9g00iVR:g00AkR;#_R<#7R=#7R>#7R?#7R@#7RA#J%7ARA#7#_#H#HRB#7#_#H#H#H#H#H#JRC3\RD%JARECn%[3RF543C;%[1R1C;RG;9GP5P6P0P2%08#^#G#K#B#gg00e]P9PDPECn=43FC;P1C;R1=971RF%Z4R3%38RE%08R9#0RH#0RI#0RJ#0RK#0RL#R#5RM#5RN#3RO5XC%J;RC%1I#R#ePA%08#E#E#5#2#ACd%3JRJ,cC%18RP#1RQ#1RR#<#<#<RS#5#D#D#D#2%0N#R#5RN#0#5#D#D#25XC1oCNRT%3NRN']PC%RR#ePAg00jnRR#ARUCdPC%RQRQ#0RV#0PAPUPC%0PRP#QPAPUPC%5PPAPUPC%19RP#QPA%3K#A9\:CPC%5PPA%08#E#8#:#2#APC%QHPA%39#APCPLPA%3I#ARI9\:CPCPVPA%b8#L#<#G#2#A%J@R@%O8#B#D#2RV%^S#<RS#=#<#E#5#D#23X1c@JPTPN1@@RR@POCz%=Q#D#2,@U%=8#6#D#2']%88#G#M#Q%18#=#K#G#8#b#3%18#V#M#:#V#3%R8#V#M#:#V#3%P8#>#E#E#2%08#6#8#>#8%O8#:#5#L#2%P8#>#E#<#2RQ,@UPA%AQ%P8#>#<#:#2,@UP>%J?R?%08#6#G#L#>%P8#>#<#E#2%08#6#G#<#8%P8#:#5#>#2%08#6#8#5#8%P8#:#5#B#2%08#6#8#>#5%08#6#8#>#=#2%18#6#8#6#5%O8#:#K#K#2R>1@U>?yI<%=8#=#B#=#G#5%O8#:#K#M#2'x%=8#=#B#=#8#V#3%18#6#L#B#=#2RI1@UIPA%J=%18#6#L#B#8%O8#:#K#8#2%18#6#L#M#Q%O8#:#K#<#2R=1@U=PA%3MRM#A%18#6#L#Q#5%O8#:#B#B#2%18#6#<#M#6%3S9X?E1NRM%[4R43I7?V3?Cm3?3?Cm3w3I3?3?3?3?3?Fv3?Du5tO3I3IDFDFDFDFDFDFDFDF3I3I3IRV;9VRMg00@ARR#ZR?/Y3REP?P3%[RRS94R;1]@O/s4R4C;R@;9@ROP?P3A4RBS94R;P4C;R4=9E4RRg00f=RS?9DDR8'CRA'CR='CRI'C1S7GPFPI1S71PMP=1S3VPOPA1SE@PRP81SE41SSDCUCUCUCUCUP5P6P0P2g00BJR81Y82RRg00CXRAg01B43WRO7W2RV#kAi82OC;%fVC;=97GP5P6P0P2g01C1R09WRARA9W82RR#kAi82AC;%fRC;=971g01@D,r0g01CnR0593P?P3g01DkR1g00F\R7g01Ehg00HSP;Dh1j17#a,l0C;=9E@P?P3g01FfR3P7g01GcR?g01HaP;Dh1j37#a,l0C;=9E4PSPBP?PUCq=9SD'C'C'C'C'Cdo"). Qed.
End VP1.
