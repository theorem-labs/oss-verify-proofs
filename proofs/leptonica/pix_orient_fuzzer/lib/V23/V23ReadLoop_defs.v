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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23OpenFail_defs V23Open_defs V23Oom_defs V23DirRead_defs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23ReadLoop_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingI47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00K47Corelib4Init9Datatypes3nat01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs3e_rc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5e_rvlc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4e_src5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4sr_Lc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4e_knc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5kn_MLK47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall9log_win_bC5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs8kn_afterC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24ridxC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sr_updC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:sr_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<LibKnowFrame8kn_frameK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_srAnK47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib7Numbers7BinNums1Z01c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_rAnc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6want_xc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_rAtc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_knAc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_srAtK47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_knRc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4l_rCc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_srCc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_rC2c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5h_rvlc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_srC2c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4sr_Hc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_knC2C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive?sr_after_call_jC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall7kn_callc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_srBc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4l_rBc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_knBC5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs7KEPT_MCc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_srD0C5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3IHIc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_knD0K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_rDnc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_rDtc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5l_knDc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5d_rvlc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_srDnc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs5f_rvlc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs6l_srDtc5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs4sr_F".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSL : list Z := (0x6320c :: 0x6323c :: 0x631d4 :: STOPS3)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSL scr ss [].
Definition NXL : nat := 41.
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_L : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x1381d0; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; ELit 3; EVar 8; ELit 0x127f09; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x1381d0; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_F : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x1381d0; J 5; J 6; J 7;
   ELit 2; J 9; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 8; ELit 3; EVar 8; ELit 0x127f09; EVar 6;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_ML : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-8388608)) 8388608;
   (* [comment removed for export] *)
   KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-88)) 8 (spx 32); KWord (SA (EVar 0) (-80)) 8 (ELit 0x63140);
   KWord (SA (EVar 0) (-72)) 8 (ELit 2); KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-56)) 8 (ELit 0x10df20);
   (* [comment removed for export] *)
   KRange (EVar 6) 0x159000 0x7fffff7f0000; KAlign (EVar 6) 16; KWr (SA (EVar 6) 0) 65536;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 6) 0) 65536;
   (* [comment removed for export] *)
   KWr (SA (ELit 0) 0x127000) 204800;
   KImg 0x10000 0x127ec0; KImg 0x127ec1 0x127f09; KImg 0x137f09 0x138100; KImg 0x1381e8 0x1581f8;
   KWord (SA (ELit 0) 0x138108) 8 (ELit 0x138108); KWord (SA (ELit 0) 0x138128) 4 (EVar 5);
   KImg 0x138134 0x138180; KImg 0x138188 0x1381a0; KImg 0x1381a8 0x1381c0; KImg 0x1381d0 0x1381e0; KImg 0x158210 0x158440;
   KBlob (SA (ELit 0) 0x158440) (ELit 8) 2; KImg 0x158448 0x158450; KImg 0x158461 0x158468;
   KWord (SA (ELit 0) 0x158468) 8 (EVar 3); KImg 0x158470 0x158478; KImg 0x158488 0x158490;
   KWord (SA (ELit 0) 0x158490) 8 (ELit 4096); KImg 0x158498 0x1584c8; KImg 0x158890 0x159000;
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
Definition l_ssA : sym_state := SS 0x6320c sr_L [] kn_ML NXL.
Definition l_rAn := Eval vm_compute in runL (SCR [false] [] []) l_ssA.   (* [comment removed for export] *)
Definition l_rAt := Eval vm_compute in runL (SCR [true] [] []) l_ssA.    (* [comment removed for export] *)
Definition l_srAn : list expr := Eval vm_compute in s_regs (fst (fst l_rAn)).
Definition l_srAt : list expr := Eval vm_compute in s_regs (fst (fst l_rAt)).
Definition l_knA : list kentry := Eval vm_compute in kn_after l_rAn kn_ML.
(* [comment removed for export] *)
Definition l_srR (e : expr) : list expr := sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) e.
Definition l_knR : list kentry := Eval vm_compute in kn_frame l_knA (ELit 0) 0x127f09 65536.

(* [comment removed for export] *)
Definition l_rC := Eval vm_compute in runL scr0 (SS 0x11eff4 (l_srR (ELit 0)) [] l_knR 42).
Definition l_srC : list expr := Eval vm_compute in s_regs (fst (fst l_rC)).
Definition l_knC : list kentry := Eval vm_compute in kn_after l_rC l_knR.
Definition l_rC2 := Eval vm_compute in runL scr0 (SS 0x11eff4 (sr_upd l_srC (ridx 10) (ELit 0)) [] l_knC 42).
Definition l_srC2 : list expr := Eval vm_compute in s_regs (fst (fst l_rC2)).
Definition l_knC2 : list kentry := Eval vm_compute in kn_after l_rC2 l_knC.
Definition h_rvl : list expr := rvl9 (EVar 6) (EVar 7) (EVar 8) l_srC2.

(* [comment removed for export] *)
Definition l_knRB : list kentry := KRange (EVar 42) 1 65536 :: l_knR.
Definition l_rB := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x11eff4 (l_srR (EVar 42)) [] l_knRB 43).
Definition l_srB : list expr := Eval vm_compute in s_regs (fst (fst l_rB)).
Definition l_knB : list kentry := Eval vm_compute in kn_after l_rB l_knRB.

(* [comment removed for export] *)
Definition l_srD0 : list expr := Eval vm_compute in sr_after_call_j l_srB KEPT_MC 43.
Definition l_knD0 : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x127000 l_knB.
Definition l_rDn := Eval vm_compute in runL (SCR [false] [] []) (SS 0x631c0 l_srD0 [] l_knD0 75).  (* [comment removed for export] *)
Definition l_rDt := Eval vm_compute in runL (SCR [true] [] []) (SS 0x631c0 l_srD0 [] l_knD0 75).   (* [comment removed for export] *)
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
  (s_pc (fst (fst e_r)), snd (fst e_r), s_log (fst (fst e_r))) = (0x6320c%Z, [], [])
  /\ (sr_mismatch e_rvl idb e_sr sr_L 0, kn_missing e_kn (map (kmap e_rvl idb) kn_ML)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23ReadLoop_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j16Tg000Pj27Tg0010j11Tg001Uj15Tg002:j1@Tg002Xj14Tg0038j40Tg003Xj33Tg0042j3;Tg004Rj28Tg004lj4:Tg005Gj39Tg005dj1DTg006kj3CTg007Hj1BTg008Pj5?Tg009]j2=Tg00:cj4>Tg00;?j2<Tg00<Kj2ATf0#5#5p=2g00<fR0g00=DR1#6R2'7R3g00>QR4#6R5'7R6P3P5P0P2g00?\#1#5#2#1#1#2#1#5#2#2#1#1#2#@%41C0%44C0R4;34g00@AR1#6R7g00@`R8#6R9'7R:P7P9g00AkR;%415;1%48C0R1;31186418:1C:P3P5P0P2g00BJR01702g00CXg00Dd39R5792R3#DAC025C0%B3C0=364P7P9g00EaR9g00F`R7g00G]g00H[P;D?g00IYP8P81=97g00JWC>'<C0=3:1'Ado"). Qed.

Lemma l_itinA :
  (s_pc (fst (fst l_rAn)), snd (fst l_rAn), log_win_b 0 (s_log (fst (fst l_rAn))))
    = (0x11eff0%Z, [SCBr false BC_LTU want_x (ELit 65536)], true)
  /\ (s_pc (fst (fst l_rAt)), snd (fst l_rAt), log_win_b 0 (s_log (fst (fst l_rAt))))
    = (0x11eff0%Z, [SCBr true BC_LTU want_x (ELit 65536)], true)
  /\ kn_after l_rAt kn_ML = l_knA
  /\ (nth 17 l_srAn (ELit 0), nth 10 l_srAn (ELit 0), nth 11 l_srAn (ELit 0), nth 12 l_srAn (ELit 0))
     = (ELit 63, ELit 3, ELit 0x127f09, ELit 65536)
  /\ nth 12 l_srAt (ELit 0) = want_x
  /\ sr_upd l_srAt (ridx 12) (EVar 41) = sr_upd l_srAn (ridx 12) (EVar 41)
  /\ sr_vars_lt 41 l_srAn = true /\ sr_vars_lt 41 l_srAt = true /\ kn_vars_lt 41 l_knA = true
  /\ kn_frame l_knA (ELit 0) 0x127f09 65536 = l_knR
  /\ sr_vars_lt 42 (sr_upd l_srAn (ridx 12) (EVar 41)) = true /\ kn_vars_lt 42 l_knR = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V23ReadLoop_defs ()) ["VP1"] "p&0p;1p;2p;3p;4g0000j1jTg000Pj2XTg001Uj10Tg00KVj1_Tg00L4j1ITg00M=j13Tg00M\j1?Tg00Nek307Tg00Onj3cTg002:j15Tg00Q7j4bTg002Xj1hTg0042j34Tg003Xj39Tg00RDj2mTg0010j11Tg00SOj3eTg00TZj2dTg00Uej2DTg00Vok406Tg00X:k304Tg00YEj2NTg0038j4ATg00<Kj2:Tg004Rj2RTg004lj4gTg005Gj3`Tg005dj1qTg006kj3pTg007Hj1oTg00ZPj2kTg00[Wj2}Tg00\Yj4nTg00]5j1|Tg00]Sj2{Tg00^6j3zTg00^Yj1yTg00_`j3rTg00`ij2iTg00b0j2tTg00c7j4xTg00dBj3]Tf0R0#0#0p=J%10#1#1#1p==%00#1p=F%10#1#1#0p=U%00#0#0#5p=<%30#3p=@%00#0#0#0p=2g00<fR1f2R2f1R3P0CAp=TP3g00eMR4P0g00emR5CAp=a%10#0#0#0p=7%10#0p=G%00#0#1#1p=>%00#0#1#0p=8%50#Ip=C%10#1p=f%00#0#0#0#0#0#0#0p=P%00#0#0#0#0#0#0#5p=M%_0,D3p=w%00#_p=lf3R6/D2?]30p=v%00#0#0#1p=O%00#1#0#0p=;%10#0#1#1p=W%00#1#1#1p=E%10#1#0#0p=6%50,N3p>05%10#0#0#1p=L%00#0#1p=V%00#1#0p=Q%53/N0p>03g00@`R7A4730742p=S%02#5/N3=470p=KA]623=470p=u1N23=470p>02%03#5,N2=470p>01f6R8f5R9f4R:3]A]623=470547p>001N:61N23=470547p=~%_6,D:?]23=470p=Hg00fMR;%?3;40p=s%?2%?3=4;054;p=ZA4;3094;2p=BP8P9P:P6P2P3P0CgCgp=\P;P3g00gVR6P0Cnp=^A9405p=[1:30,:2p=Yg00=DR2#jR3,X1R1/X4R0g00?\R:#0#J#=#F#=#U#<R9g00hVR8g00i6R<g00ihR=g00jT%_:#Ig00AkR>#@R?#3R@#3RA#3RB#3RC#3RD#?RE407%3DRD#?RF3cRG%0:RH#0RI#0RJ#0RK#0RL#0RM#J#2RN#2RO#5RP#IRQCb%h2RR5425T3,a1RS;9SP5P<PGPQCb=42R9T39,a1RT=90TRU%j7RV%?>RW%7JPD%G:#>#8#8#7#C%5KRX,mW%1:RY#1RZ#1R[#fR\#f#=#=R]#P#P#P#M%0O#J#2RO#0#P#P#M5eW1wWOR^%5ORO'dPW%J[#lPDg00k@R[#IR_CvPW%0Z#JRZ#0PDP_PW%0YR`#7PDP_PW%0`R`#0#JPDP_PW%1HRa#7PD%CL9c=WPW%2aPD%G:#>#O#;#2#CPW%7IRIPD%CHRHPWPMPD%CJRJ9c=WPWPZPD%J:#>#F#=#8#2#C%?CRC%0:#W#8#2#MRZ%f]#=R]#G#=#U#P#M3e1mCX1DC[RX/dPP^POPXPPH06%0:#;#U#2#M,D_%1`#J#2#M'd%8:#E#U#6#2-05P%8:#E#U#6#O#5%8:#E#=#2#L#5RX%>:#E#=#2#L#5%0:#E#2#8#M%V:#6#2#=#;%0:#W#2#>#=#<%0:#E#2#8#O#<RO,D_PD%IO%V:#6#2#L#F#<,D_PA%?BRB%V:#6#2#L#G#G%0:#E#2#>#M%V:#6#2#6#;%0:#E#2#>#;#<%0:#E#2#>#F#;%0:#E#2#>#7#<%V:#6#2#U#G#<RA%V:#6#2#=#2%Q:#6#O#2#7%0:#W#2#7#7#<RO1D_O@04J?%F:#F#7#;#;#7%Q:#6#8#8#G#<+03%F:#F#G#O#O#G#O#5%Q:#6#8#>#F#<RJ1D_JPD%?@%Q:#6#8#>#7%0:#W#2#7#=#<%Q:#6#8#;#;%0:#W#2#L#8#<R@1D_@PD%5NRN#I%Q:#6#8#;#6%0:#W#2#L#L#<%Q:#6#;#;#7%5:%5]5eB1N[N%h73S7KZ3KCu3K3KCu4023S3K4013K3K3KK003KD~3S3S3SDHDHDHDHDHDHDHDH3S3SDHRZ;9ZR71X;;RN/X;R[/X;RBP[P;PNP;P;P;%C\R\%CYRYCA%IXR]CAPQCAR@;9@RJA9;GGRO%j;R^%J:#7#L#F#L#7#C%lI#I9c=W%7K#P#C%IA%@DRD#3RA#3RK#@RW#?%3WRW%3WRW%3WRW#3#@#@#@#@#@#@#@R=#3RI#3R:#3RM#3RL#3Rb#3Rc#3Rd#3Re#3Rf#?Rg%h;,se9Zcd9ZLb9Z:M9Z=I9BF]9BEY,s?9B_\9B__7B_9BY]9BHC3Z3B3B5B_RC;9CRHA9455R]1:]]RY,:7R\,:]R?,:]RE':RF':RI':R=':RM':R:':1R0SPUP:1R0TP7PM1RVZRZPJP=1RB@POPI1R;GPHPF1R^CP]PE1R45REP]P?PEP]P\PEP7PYPZP]P]PEPECgF\F\F\F\F\P1P4g00BJRE1XE3R]g00CXRZg00k^3`RY7`3R7#qApE3Y5T3%o7,k>CAP8P<g00l]R8PQCb=42R9T39,a1590P1P4g00m]R49`]ZRZ9`E3R]#qApE3Z5T3%o],k>CAP5P<P8PQCb=42R9T39,a1590g00JW,}4g00n\R459VP[P;PNP;P;P;1^W_1^D_CA1^A_CA1^K_CA=9B@P;PKg00o[RKP_Cn=9;8%|aRa%5`R`g010[1{a`d3z#yR`=rKgAr6`gR`59^1if6#[1ifK#[1tf4#[P4P_PXPPCxg0117RP59V%3fRf/i`#[1tfP#[':3Y3Y3Y3Y3Ydo"). Qed.

Lemma l_itinC :
  (s_pc (fst (fst l_rC)), snd (fst l_rC), log_win_b 0 (s_log (fst (fst l_rC))), nth 17 l_srC (ELit 0), nth 10 l_srC (ELit 0))
    = (0x11eff0%Z, [], true, ELit 57, ELit 3)
  /\ (s_pc (fst (fst l_rC2)), snd (fst l_rC2), s_log (fst (fst l_rC2))) = (0x6323c%Z, [], [])
  /\ (sr_mismatch h_rvl idb l_srC2 sr_H 0, kn_missing l_knC2 (map (kmap h_rvl idb) kn_ML)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23ReadLoop_defs ()) ["VP1"] "p;1p;2p;3p;4p;5g0000j1<Tg000Pj23Tg001Uj15Tg002:j1:Tg002Xj1;Tg0010j14Tg00L4j1>Tg003Xj36Tg0038j48Tg00<Kj2=Tg004Rj2@Tg004lj4ETg005Gj39Tg005dj1DTg006kj3CTg007Hj1BTg00ZPj2JTg00M=j1?Tg00\Yj4ATg008Pj5ITg009]j2HTg00:cj4FTg00;?j2GTf0R0#5#5p=1%40#4p=0f6f5f4f3f2f1C8P0C8p=7%?0#?p=2g00<fR0g00=DR1#<R2'3R3g00eMR4'3R5g00fMR6'3R7/36R8P7P6P5P6P3P4P0P2g00?\R9#5#1#0#0#5#0#0#0#0#1#1#:%;1R1g00emF7%49R:#4#1#4#:#>%::#>F7R:;6:g00>QR;#<R<,33R=P3P<P0P2%49#5#1#0#1#4#5#1#0#0#1#:P1%;;F7R;;6;R1g00@AR9#<R>g00@`R?#<R@'3RAP>P@%;9%;?C8R9;69RB'=1@8:P1PB1@=;1@A9CECEP7P6P5P6P3P4P0P2g00BJR41342R5g00CXR7g012639RB792R1#DAC42Bg00AkRB%B1'JF7P6%2B#2#2#2#2R1#?#2#2#2g0134RCg00k@#>RDCAP6P1PCPDCAF7=68:P3P<P0P2g01439957R79942R5#DAC427%B5F7=6=;P>P@g0152R@g00F`R>g0161g0171PBDIg017oP?P?1H@>g00JWCF'GC8=6A9'='=do"). Qed.

Lemma l_itinB :
  (s_pc (fst (fst l_rB)), snd (fst l_rB), log_win_b 0 (s_log (fst (fst l_rB)))) = (0x11e154%Z, [], true)
  /\ (nth 1 l_srB (ELit 0), nth 10 l_srB (ELit 0), nth 11 l_srB (ELit 0), nth 12 l_srB (ELit 0))
     = (ELit 0x631c0, EAlu ALU_ADD (EVar 6) (EVar 7), ELit 0x127f09, EVar 42)
  /\ sr_vars_lt 43 l_srB = true /\ kn_vars_lt 43 l_knB = true
  /\ sr_after_call_j l_srB KEPT_MC 43 = l_srD0 /\ kn_call [] 0 0 IHI 0x127000 l_knB = l_knD0 /\ kn_vars_lt 43 l_knD0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V23ReadLoop_defs ()) ["VP1"] "p;1p;2p;4p;3p;6g0000j1bTg000Pj2TTg001Uj10Tg002Xj1\Tg0038j4?Tg003Xj3ATg00M=j11Tg00M\j1BTg00Onj3^Tg002:j15Tg00L4j1OTg00KVj1_Tg0010j12Tg00SOj3ZTg00RDj2dTg00TZj2cTg00Uej2CTg00Voj4zTg00X:j3yTg00YEj2RTg00<Kj2>Tg004Rj2YTg004lj4WTg005Gj3gTg005dj1sTg006kj3rTg007Hj1qTg00ZPj2pTg00`ij2nTg00b0j2iTg018oj3mTg01:=j6tTg0042j37Tg00dBj3XTg00\Yj4lTf0R0#0#0#2#2p=8%20#2#0#0p=6%00#0#2#0p=9%20#0p=4%00#5p=o%00#0#0#2p=I%00#0#0#0p=3%50#Op=G%00#2#2#2p=F%20#2#2#2p=;%20#0#0#2p=L%10#1p=`%10#1#1#1p=@%20#0#0#0p=:%00#0#0#0#0#0#0#0p=N%00#0#0#5p=<g00fMR1f2R2#Bf1R3#B=71037p=KA71309712p=V%B3=710p=[%00#0p=J%00#_p=ff3R4/C2?X30p=e%00#0#0#0#0#0#0#5p=H%_0,C3p=k%00#2#0#0p==%00#2p=E%20#0#2#2p=U%20#2p={%00#0#2p=S%00#2#0p=Q%53/R0p=xg00@`R5A7530772p=P%02#5/R3=750p=DAX423=750p=j1R23=750p=w%03#5,R2=750p=hf6f5f4R63XAX423=750575p=v1R641R23=750575p=u%_4,C6?X23=750p=MP1P3g01;BR3P0Clp=]g00eMR2g00emR67A0p=ag00<fR0g00=DR4#bR7'TR8/T2R9P8P2P0P7g00?\R:#0#8#6#9#4#4#4#o%\4C?P6C?R4;A41T11R;/T1R</T1R=P<P1P;P1P1P1%4:#8#I#6#3#GR>g00ihR?g00AkR@#1RA#1RB#1RC#1RD#1RE#1RF#BRG%1FRF#BRH3^RIC?%9:#F#;#3#L#5RJ#ORKC?%1FRF#`RL#1RM#1RN#1#@#@#@#@#@RO#1RP#1RQ#1RR#`#@RS#BRTC?RU;AURVAA266RW%b1RX%1SRS%B@RY%0:RZ#0R[#0R\#0R]#0R^#0R_#0R`#_#O5^?%:]#N#G%0:#F#3#8#4#4#<Ra#O%1S#@Rb%1bRb%1bRb%GZRc%@bRb#B%1bRb%1bRb%1bRb%1bRb%1bRb%1bRb%2:Rd#G%1b#`#@#@Rb%1bRb%1bRb%1b%\13K3K9KQR9KOP9VKT,[F5VH,[B3K3K3K5VI7VG'[3K3V5V>'[R>;A>RI%b5RH%5:RK%0`#3R`#3RP#5RO5ZTPY%2\#J#fPF%4:#8#9#9#:#GCe%5]R],dY%2dRT#2RR#;#;#;RQ#N#N#N#H%0P#J#3RP#0#N#N#H5ZY1kYPRb%5PRP'cPY%JR#fPFg00k@RR#OReCePY%0T#JRT#0PFPePY%0dRd#:PFPePY%0dRd#0#JPFPePY%2ZRZ#:PF%G^9^?YPY%3ZPF%4:#8#I#=#3#GPY%:[PFPcPYP_PF%G\R\9^?YPYPTPF%J:#8#E#;#9#3#G%0:#U#9#3#HRT%{Q#;RQ#U#;#4#N#H5ZG1dG]PbPP1CGRPOCz%S:#8#4#3#HRG,Ce%2d#J#3#H'c%S:#8#;#E#4#3%J:#L#;#4#6#I#5PJ%8:#F#;#3#L#5%0:#F#3#9#H%S:#6#3#;#=%0:#U#3#8#;#<%0:#F#3#9#I#<RJ,CePF%OJ%S:#6#3#L#E#<,CePD%BERE%S:#6#3#L#4#4%0:#F#3#8#H%S:#6#3#6#=%0:#F#3#8#=#<%0:#F#3#8#E#=%0:#F#3#8#:#<%S:#6#3#;#3%Q:#6#I#3#:%0:#U#3#:#:#<RD1CeD?y\B%E:#E#:#=#=#:%Q:#6#9#9#4#<'x%E:#E#4#I#I#4#I#5%Q:#6#9#8#E#<R\1Ce\PF%BC%Q:#6#9#8#:%0:#U#3#:#;#<%Q:#6#9#=#=%0:#U#3#L#9#<RC1CeCPF%5`R`#O%Q:#6#9#=#6%0:#U#3#L#L#<%Q:#6#=#=#:%5Q9ZEK1RR`%\53P7DT3DCj3D3DCj3w3P3D5ha3D3D3DFv3DDu5hO3P3PDMDMDMDMDMDMDMDM3P3P3PRO;AORa/>WRT'>R5,>WR`'>RE'>1Y94PVPE1Y=UPWP`1Y26R6PWP5P6PIPT1YX>PaPW1YHOP6CWCWCWCWCWCWP8P2P0P7g00BJR21T27g00CXg01<A3gR87g7R6#sAr278C?%q6,p@C?=A94P<P1P;P1P1P11]Ae1]LeC?1]MeC?1]NeC?=A=U1nS3#ag01=?RU,iS#ag01>>=m3Sg01??5AX1T00#\PRPRg01@?PGPUEtg01A<RU5AH1iSU#a'>'>'>'>'>'>do"). Qed.

Lemma l_itinD :
  (s_pc (fst (fst l_rDn)), snd (fst l_rDn), s_log (fst (fst l_rDn)))
    = (0x6320c%Z, [SCBr false BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ (s_pc (fst (fst l_rDt)), snd (fst l_rDt), s_log (fst (fst l_rDt)))
    = (0x631d4%Z, [SCBr true BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ kn_after l_rDt l_knD0 = l_knD
  /\ (sr_mismatch d_rvl idb l_srDn sr_L 0, kn_missing l_knD (map (kmap d_rvl idb) kn_ML))
     = ([0%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ (sr_mismatch f_rvl idb l_srDt sr_F 0, kn_missing l_knD (map (kmap f_rvl idb) kn_ML))
     = ([0%nat; 19%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ nth 19 l_srDt (ELit 0) = EAlu ALU_ADD (EVar 7) (EVar 42).
Proof.
ltac2:(KReplay.run1 (kr_t_V23ReadLoop_defs ()) ["VP1"] "p;1p;2p;3p;4p;5g0000j1\Tg000Pj2ZTg0010j11Tg00M=j18Tg00M\j1LTg00Onj3]Tg00Q7j4nTg002Xj1[Tg0042j34Tg0038j4<Tg003Xj3;Tg002:j13Tg001Uj10Tg00SOj3YTg00L4j1ATg00RDj2bTg00TZj2^Tg00Uej2@Tg00Voj4{Tg00X:j3zTg00YEj2OTg00<Kj2BTg004Rj2QTg004lj4STg005Gj3XTg005dj1jTg006kj3iTg007Hj1fTg00[Wj2sTg008Pj5eTg009]j2mTg00;?j2kTg00\Yj4rTg00KVj1`Tg00dBj3UTg00:cj4qTf0R0#0#0#0#1p=C%10#0#0#1p=I%00#0#0#0p=2%00#1#1#0p=T%00#3p=h%80#8p=_%80#8#8#8p=K%10#0#0#0p=5%10#1#1#0p=R%10#0p=V%00#0p=F%00#`p=d%00#1p=E%00#0#0#3p=6f3R1f2R2'@f1R3;U0p=c%10#1#1#1p==%00#0#0#0#0#0#0#0p=P%00#0#0#0#0#0#0#3p=G%`0,@3p=p%00#0#1#0p=9%10#0#1#1p=J%00#1#0#0p=:%10#1p=o%00#0#1p=W%00#0#1#1p=?%00#1#1#1p=a%10#1#0#0p=7%00#0#1#1#1#0#0#0#0p=D%00#1#0p=N%33/O0p=yg00@`R4A4430742p=M%02#3/O3=440p=>AU123=440p=l1O23=440p=xf6f5f4R53UAU123=440544p=w1O511O23=440544p=v%03#3,O2=440p=u%`1,@5?U23=440p=HA4430p=tP4P4P0g00JWCqp=gg00<fR0g00=DR3#\R2'ZR5g00>QR1#\R6'ZR7P5P6P0P2g00?\R8#1#C#I#2#T#hg00hVg01B<R9g00ihR:g00AkR;#_R<#8R=#8R>#8R?#8R@#8RA#L%8ARA#8#_#K#KRB#8#_#K#K#K#K#K#LRC3]RD%LARECn%[3RF543C<%[1R1C<RG;;GP5P6P0P2%18#C#5#R#V#V#hg00emP9PDPECn=43FC<P1C<R1=;71RF%\4R3%38RE%08R9#0RH#0RI#0RJ#0RK#0RL#F#2RM#2RN#3RO5YC%L;RC%1I#F#dPA%18#C#I#C#E#6#ACc%3JRJ,bC%18RP#1RQ#1RR#=#=#=RS#P#P#P#G%0N#F#2RN#0#P#P#G5YC1pCNRT%3NRN'^PC%FR#dPAg00k@RR#ARUCcPC%0Q#FRQ#0PAPUPC%0PRP#5PAPUPC%0PRP#0#FPAPUPC%19RV#5PA%3K#A9]:CPC%2VPA%18#F#T#9#5#6#APC%5HPA%39#APCPLPA%3I#ARI9]:CPCPQPA%08#C#J#R#:#6#A%L@R@%08#J#9#2#GRQ%oS#=RS#V#=#R#P#G3Y1b@JPTPN1@@RR@POC{%08#:#R#2#G,@U%1P#F#2#G'^%W8#?#=#T#2%98#a#R#7#C#3%98#a#=#2#I#3%?8#a#=#2#I#3%D8#9#G%W8#7#2#=#:%08#J#2#?#=#6%D8#9#C#6RP,@UPA%AP%W8#7#2#I#E#6,@UP>%L?R?%D8#9#T#V%D8#?#G%W8#7#2#7#:%D8#?#:#6%D8#?#E#:%D8#?#5#6%W8#7#2#R#5%D8#?#7#6%N8#7#C#2#5%08#J#2#5#5#6R>1@U>?zI<%E8#E#5#:#:#5%N8#7#9#9#V#6'y%E8#E#5#:#T#C#3%N8#7#9#?#E#6RI1@UIPA%L=%N8#7#9#?#5%08#J#2#5#=#6%N8#7#9#:#:%08#J#2#I#9#6R=1@U=PA%3MRM#A%N8#7#9#:#7%08#J#2#I#I#6%N8#7#:#:#5%3S9Y?E1ORM%[4R43M7>Q3>Cl3>3>Cl3x3M3>3>3>3>3>Fw3>Dv5uO3M3MDHDHDHDHDHDHDHDH3M3M3MRQ;;QRMg00@ARR#\R?/Z3REP?P3%[RRS94R;1^@O/t4R4C<R@;;@ROP?P3A4RBS94R;P4C<R4=;E4RRg00fMRS?;DDR8'BRA'BR='BRI'B1Q7GPFPI1Q71PMP=1Q3QPOPA1QE@PRP81QE41QSDCSCSCSCSCSP5P6P0P2g00BJR81Z82RRg00CXRAg01Bn3XRO7X2RQ#jAi82OC<%fQC<=;7GP5P6P0P2g01CmR09XRARA9X82RR#jAi82AC<%fRC<=;71g01A<,s0g01DlR05;3P?P3g01EkR1g00F`R7g01Fjg00H[P;De1m17#g,k0C<=;E@P?P3g01GjR3P7g01HiR?g01IiP;De1m37#g,k0C<=;E4PSPBP?PUCr=;SD'B'B'B'B'Bdo"). Qed.
End VP1.
