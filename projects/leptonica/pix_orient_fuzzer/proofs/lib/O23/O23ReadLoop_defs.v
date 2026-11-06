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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23OpenFail_defs O23Open_defs O23Oom_defs O23DirRead_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23ReadLoop_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs3e_rC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5e_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4e_srC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4sr_LC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4e_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5kn_MLC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver<LibKnowFrame8kn_frameC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_srAnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_rAnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6want_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_rAtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_knAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_srAtC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_knRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4l_rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_srCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_rC2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5h_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_srC2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4sr_HC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_knC2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_srBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4l_rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_knBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_srD0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_knD0C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_rDnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_rDtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5l_knDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5d_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_srDnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs5f_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs6l_srDtC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23ReadLoop_defs4sr_FC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPSL : list Z := (0x62be8 :: 0x62c18 :: 0x62bb0 :: STOPS3)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSL scr ss [].
Definition NXL : nat := 41.
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_L : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x123d20; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; ELit 3; EVar 8; ELit 0x113a59; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x123d20; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_F : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x123d20; J 5; J 6; J 7;
   ELit 2; J 9; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 8; ELit 3; EVar 8; ELit 0x113a59; EVar 6;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_ML : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-8388608)) 8388608;
   (* [comment removed for export] *)
   KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-88)) 8 (spx 32); KWord (SA (EVar 0) (-80)) 8 (ELit 0x62b1c);
   KWord (SA (EVar 0) (-72)) 8 (ELit 2); KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-56)) 8 (ELit 0xf9a7c);
   (* [comment removed for export] *)
   KRange (EVar 6) 0x145000 0x7fffff7f0000; KAlign (EVar 6) 16; KWr (SA (EVar 6) 0) 65536;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 6) 0) 65536;
   (* [comment removed for export] *)
   KWr (SA (ELit 0) 0x113000) 204800;
   KImg 0x10000 0x113a10; KImg 0x113a11 0x113a59; KImg 0x123a59 0x123c50; KImg 0x123d38 0x143d48;
   KWord (SA (ELit 0) 0x123c58) 8 (ELit 0x123c58); KWord (SA (ELit 0) 0x123c78) 4 (EVar 5);
   KImg 0x123c84 0x123cd0; KImg 0x123cd8 0x123cf0; KImg 0x123cf8 0x123d10; KImg 0x123d20 0x123d30; KImg 0x143d60 0x143f90;
   KBlob (SA (ELit 0) 0x143f90) (ELit 8) 2; KImg 0x143f98 0x143fa0; KImg 0x143fb1 0x143fb8;
   KWord (SA (ELit 0) 0x143fb8) 8 (EVar 3); KImg 0x143fc0 0x143fc8; KImg 0x143fd8 0x143fe0;
   KWord (SA (ELit 0) 0x143fe0) 8 (ELit 4096); KImg 0x143fe8 0x144018; KImg 0x1443e0 0x145000;
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
Definition l_ssA : sym_state := SS 0x62be8 sr_L [] kn_ML NXL.
Definition l_rAn := Eval vm_compute in runL (SCR [false] [] []) l_ssA.   (* [comment removed for export] *)
Definition l_rAt := Eval vm_compute in runL (SCR [true] [] []) l_ssA.    (* [comment removed for export] *)
Definition l_srAn : list expr := Eval vm_compute in s_regs (fst (fst l_rAn)).
Definition l_srAt : list expr := Eval vm_compute in s_regs (fst (fst l_rAt)).
Definition l_knA : list kentry := Eval vm_compute in kn_after l_rAn kn_ML.
(* [comment removed for export] *)
Definition l_srR (e : expr) : list expr := sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) e.
Definition l_knR : list kentry := Eval vm_compute in kn_frame l_knA (ELit 0) 0x113a59 65536.

(* [comment removed for export] *)
Definition l_rC := Eval vm_compute in runL scr0 (SS 0x10ab50 (l_srR (ELit 0)) [] l_knR 42).
Definition l_srC : list expr := Eval vm_compute in s_regs (fst (fst l_rC)).
Definition l_knC : list kentry := Eval vm_compute in kn_after l_rC l_knR.
Definition l_rC2 := Eval vm_compute in runL scr0 (SS 0x10ab50 (sr_upd l_srC (ridx 10) (ELit 0)) [] l_knC 42).
Definition l_srC2 : list expr := Eval vm_compute in s_regs (fst (fst l_rC2)).
Definition l_knC2 : list kentry := Eval vm_compute in kn_after l_rC2 l_knC.
Definition h_rvl : list expr := rvl9 (EVar 6) (EVar 7) (EVar 8) l_srC2.

(* [comment removed for export] *)
Definition l_knRB : list kentry := KRange (EVar 42) 1 65536 :: l_knR.
Definition l_rB := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x10ab50 (l_srR (EVar 42)) [] l_knRB 43).
Definition l_srB : list expr := Eval vm_compute in s_regs (fst (fst l_rB)).
Definition l_knB : list kentry := Eval vm_compute in kn_after l_rB l_knRB.

(* [comment removed for export] *)
Definition l_srD0 : list expr := Eval vm_compute in sr_after_call_j l_srB KEPT_MC 43.
Definition l_knD0 : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x113000 l_knB.
Definition l_rDn := Eval vm_compute in runL (SCR [false] [] []) (SS 0x62b9c l_srD0 [] l_knD0 75).  (* [comment removed for export] *)
Definition l_rDt := Eval vm_compute in runL (SCR [true] [] []) (SS 0x62b9c l_srD0 [] l_knD0 75).   (* [comment removed for export] *)
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
  (s_pc (fst (fst e_r)), snd (fst e_r), s_log (fst (fst e_r))) = (0x62be8%Z, [], [])
  /\ (sr_mismatch e_rvl idb e_sr sr_L 0, kn_missing e_kn (map (kmap e_rvl idb) kn_ML)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadLoop_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j14Tg000Pj26Tg0010j10Tg001Uj11Tg002:j1CTg002Xj15Tg0038j42Tg003Xj33Tg0042j3;Tg004Rj28Tg004lj49Tg005Gj37Tg005dj1:Tg006kj3BTg007Hj1ATg008Pj5@Tg009]j2=Tg00:cj4>Tg00;?j2?Tg00<Kj2<Tg00<fR0g00=DR1#4R2'6R3g00>QR4#4R5'6R6P3P5P0P2g00?\#0#1#1#1#0#1#0#1#0#0#0#0#0#1#0#1#1#1#C%51C2%54C2R4;34g00@AR1#4R7g00@`R8#4R9'6R:P7P9g00AkR;%515;1%58C2R1;31186418:1C9P3P5P0P2g00BJR01602g00CXg00Dd37R5772R3#:AB025C2%A3C2=364P7P9g00EaR9g00F`R7g00G]g00H[P;D@g00IYP8P81=97g00JWC>'?C2=3:1'<do"). Qed.

Lemma l_itinA :
  (s_pc (fst (fst l_rAn)), snd (fst l_rAn), log_win_b 0 (s_log (fst (fst l_rAn))))
    = (0x10ab4c%Z, [SCBr false BC_LTU want_x (ELit 65536)], true)
  /\ (s_pc (fst (fst l_rAt)), snd (fst l_rAt), log_win_b 0 (s_log (fst (fst l_rAt))))
    = (0x10ab4c%Z, [SCBr true BC_LTU want_x (ELit 65536)], true)
  /\ kn_after l_rAt kn_ML = l_knA
  /\ (nth 17 l_srAn (ELit 0), nth 10 l_srAn (ELit 0), nth 11 l_srAn (ELit 0), nth 12 l_srAn (ELit 0))
     = (ELit 63, ELit 3, ELit 0x113a59, ELit 65536)
  /\ nth 12 l_srAt (ELit 0) = want_x
  /\ sr_upd l_srAt (ridx 12) (EVar 41) = sr_upd l_srAn (ridx 12) (EVar 41)
  /\ sr_vars_lt 41 l_srAn = true /\ sr_vars_lt 41 l_srAt = true /\ kn_vars_lt 41 l_knA = true
  /\ kn_frame l_knA (ELit 0) 0x113a59 65536 = l_knR
  /\ sr_vars_lt 42 (sr_upd l_srAn (ridx 12) (EVar 41)) = true /\ kn_vars_lt 42 l_knR = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadLoop_defs ()) ["VP1"] "p&0p;1p;2p;3p;4g0000j1kTg000Pj2STg001Uj10Tg00KVj1_Tg00L4j1JTg00M=j12Tg00M\j1@Tg00Nek30:Tg00Onj3cTg002:j16Tg00Q7j4bTg002Xj1jTg0042j34Tg003Xj3:Tg0010j11Tg00RDj2nTg00SOj3gTg00TZj2fTg00Uej2DTg00Vok409Tg00X:k307Tg00YEj2MTg0038j4BTg00<Kj2<Tg004Rj2OTg004lj4hTg005Gj3aTg005dj1sTg006kj3rTg007Hj1qTg00ZPj2lTg00[Wk200Tg00\Yj4pTg00]5j1~Tg00]Sj2}Tg00^6j3|Tg00^Yj1{Tg00_`j3uTg00`ij2iTg00b0j2oTg00c7j4zTg00dBj3YTf0R0#0#0#0#1p=5%00#1p=]%10#0#1#0p=E%00#1#1#0p=v%00#6p>01%20#2p=C%00#0p=K%00#0#0#0p=;g00<fR1f2R2f1R3P0CBp=QP3g00eMR4P0g00emR5CBp=d%10#0p=U%00#0#1#0p=R%10#1#0#0p=L%00#1#0#0p=8%60#Jp=G%10#1p=^%10#1#1#1p=7%00#0#0#0#0#0#0#0p=F%00#0#0#6p=3%_0,D3p=y%00#_p=mf3R6/D2?Y30p=x%10#0#0#0p=?%10#0#1#1p=e%10#0#0#1p=>%00#1#1#1p=9%00#1#0#0#0p=N%10#1#1#0p==%00#0#1#1p=\%60,M3p>08%00#0#1p=[%00#1#0p=Z%63/M0p>06g00@`R7A4730742p=P%02#6/M3=470p=IAY623=470p=w1M23=470p>05%03#6,M2=470p>04f6R8f5R9f4R:3YAY623=470547p>031M:61M23=470547p>02%_6,D:?Y23=470p=Hg00fMR;%@3;40p=t%@2%@3=4;054;p=VA4;3094;2p=AP8P9P:P6P2P3P0ChChp=WP;P3g00gVR6P0Cpp=`A:405p=X1<30,<2p=Tg00=DR2#kR3,S1R1/S4R0g00?\R:#0#5#]#]#]#E#v$01R9g00hVR8g00i6R<g00ihR=g00jT%_:#Jg00AkR>#CR?#2R@#2RA#2RB#2RC#2RD#@RE40:%2DRD#@RF3cRG%0:RH#0RI#0RJ#0RK#0RL#0RM#K#;RN#;RO#6RP#JRQCb%j2RR5425Q3,d1RS;:SP5P<PGPQCb=42R9Q39,d1RT=:0TRU%k7RV%@>RW%1J#KRX#0PD%U:#R#L#;#8#G%6KRY,nW%1:RZ#1R[#1R\#^R]#^#7#7R^#;#F#F#F#3%0O#K#;RO#0#;#F#F#35gW1yWOR_%6ORO'fPW%K\#mPDg00k@R\#JR`CxPW%0[#KR[#0PDP`PW%0ZRa#?PDP`PW%0aRa#0#KPDP`PW%1HRb#?PD%GL9c=WPW%;bPD%U:#R#e#5#L#GPW%?IRIPD%GHRHPWPMPD%GJRJ9c=WPWP[PD%1:#^#>#E#9#L#G%@CRC%N:#E#F#3R[%^^#7R^#U#7#=#;#F#33g1nCY1DC\RY/fPP_POPYPPH09%1X#U#F#3,D`%U:#8#F#3'f%5:#\#E#5#;-08P%5:#\#E#5#5#6%K:#8#=#>#]#>#6RX%K:#?#=#>#]#>#6%0:#8#9#?#E#3%[:#5#=#>#L%N:#9#E#>#3%0:#8#9#?#e#3RY,D`PD%JY%0:#8#9#?#7#3,D`PA%@BRB%[:#5#=#8#R%0:#8#9#>#E#3%[:#5#=#v#L%0:#8#9#>#=#3%[:#5#=#9#L%0:#8#9#E#R#3%0:#8#9#E#8#3RA%[:#5#=#>#?%Z:#5#=#e#;%N:#9#7#R#3RY1D`Y@07J?%8:#\#7#>#?%N:#9#7#8#3+06%8:#\#7#e#5#6%N:#9#7#9#3RJ1D`JPD%@@%Z:#5#7#=#;%N:#9#7#>#3%Z:#5#7#=#L%N:#9#7#L#3R@1D`@PD%6NRN#J%Z:#5#7#7#8%N:#?#;#\#3%Z:#R#5#7#;%6:%6^5gB1M\N%j73P7I[3ICw3I3ICw4053P3I4043I3I3IK033II023P3P3PDHDHDHDHDHDHDHDH3P3PDHR[;:[R71S;;RN/S;R\/S;RBP\P;PNP;P;P;%G]R]%GZRZCB%JXR^CBPQCBR@;:@RJA:;GGRY%k;RO%;:#=#;#7#8#G%mI#J9c=W%?K#F#G%JA%CDRD#2RA#2RK#CRW#@%2WRW%2WRW%2WRW#2#C#C#C#C#C#C#CR=#2RI#2R:#2R_#2RM#2RL#2Rc#2Rd#2Re#2Rf#@Rg%j;,te9Vcd9VML9V:_9V=I9AF^9AEZ,t?9A`]9A``7A`9AZ^9AHC3V3A3A5A`RC;:CRHA:455R^1<^^RZ,<7R],<^R?,<^RE'<RF'<RI'<R='<R_'<R:'<1O0SPUP:1O0TP7P_1OV[R[PJP=1OB@PYPI1O;GPHPF1OOCP^PE1O45REP^P?PEP^P]PEP7PZP[P^P^PEPEChFWFWFWFWFWP1P4g00BJRE1SE3R^g00CXR[g00k^3aRZ7a3R7#sArE3Z5Q3%q7,l>CBP8P<g00l]R8PQCb=42R9Q39,d15:0P1P4g00m]R49a^[R[9aE3R^#sArE3[5Q3%q^,l>CBP5P<P8PQCb=42R9Q39,d15:0g00JW-004g00n\R45:VP\P;PNP;P;P;1`W`1`D`CB1`A`CB1`K`CB=:B@P;PKg00o[RKP`Cp=:;8%~bRb%6aRag010[1}bad3|#{Ra=uKgAu6agRa5:O1if6#X1ifK#X1of4#XP4P`PXPPCzg0117RP5:V%2fRf/ia#X1ofP#X'<3T3T3T3T3Tdo"). Qed.

Lemma l_itinC :
  (s_pc (fst (fst l_rC)), snd (fst l_rC), log_win_b 0 (s_log (fst (fst l_rC))), nth 17 l_srC (ELit 0), nth 10 l_srC (ELit 0))
    = (0x10ab4c%Z, [], true, ELit 57, ELit 3)
  /\ (s_pc (fst (fst l_rC2)), snd (fst l_rC2), s_log (fst (fst l_rC2))) = (0x62c18%Z, [], [])
  /\ (sr_mismatch h_rvl idb l_srC2 sr_H 0, kn_missing l_knC2 (map (kmap h_rvl idb) kn_ML)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadLoop_defs ()) ["VP1"] "p;1p;2p;3p;4p;5g0000j1=Tg000Pj22Tg001Uj17Tg0010j16Tg002:j19Tg002Xj1:Tg00L4j1>Tg003Xj34Tg0038j48Tg00<Kj2ATg004Rj2@Tg004lj4FTg005Gj3;Tg005dj1ETg006kj3DTg007Hj1CTg00ZPj2KTg00M=j1?Tg00\Yj4BTg008Pj5JTg009]j2ITg00:cj4HTg00;?j2GTf0R0#7#7p=5%70#6p=0%60#7p=<f6f5f4f3f2f1C8P0C8p=3%?0#?p=1g00<fR0g00=DR1#=R2'2R3g00eMR4'2R5g00fMR6'2R7/26R8P7P6P5P6P3P4P0P2g00?\R9#7#5#0#0#0#0#<#<#0#6#5#9%:1R1g00emF3%69R:#<#0#9#>%9:#>F3R:;4:g00>QR;#=R<,23R=P3P<P0P2%69#5#0#0#6#5#5#0#<#5#9P1%:;F3R;;4;R1g00@AR9#=R>g00@`R?#=R@'2RAP>P@%:9%:?C8R9;49RB'A1@8:P1PB1@=;1@A9CFCFP7P6P5P6P3P4P0P2g00BJR41242R5g00CXR7g01263;RB7;2R1#EAD42Bg00AkRB%C1'KF3P6%1B#1#1#1#1R1#?#1#1#1g0134RCg00k@#>RDCBP6P1PCPDCBF3=48:P3P<P0P2g01439;57R79;42R5#EAD427%C5F3=4=;P>P@g0152R@g00F`R>g0161g0171PBDJg017oP?P?1I@>g00JWCH'GC8=4A9'A'Ado"). Qed.

Lemma l_itinB :
  (s_pc (fst (fst l_rB)), snd (fst l_rB), log_win_b 0 (s_log (fst (fst l_rB)))) = (0x109cb0%Z, [], true)
  /\ (nth 1 l_srB (ELit 0), nth 10 l_srB (ELit 0), nth 11 l_srB (ELit 0), nth 12 l_srB (ELit 0))
     = (ELit 0x62b9c, EAlu ALU_ADD (EVar 6) (EVar 7), ELit 0x113a59, EVar 42)
  /\ sr_vars_lt 43 l_srB = true /\ kn_vars_lt 43 l_knB = true
  /\ sr_after_call_j l_srB KEPT_MC 43 = l_srD0 /\ kn_call [] 0 0 IHI 0x113000 l_knB = l_knD0 /\ kn_vars_lt 43 l_knD0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadLoop_defs ()) ["VP1"] "p;1p;2p;4p;3p;6g0000j1dTg000Pj2OTg001Uj10Tg002Xj1_Tg0038j4?Tg003Xj3CTg00M=j12Tg00M\j1BTg00Onj3^Tg002:j19Tg00L4j1MTg00KVj1]Tg0010j11Tg00SOj3[Tg00RDj2nTg00TZj2mTg00Uej2ATg00Voj4|Tg00X:j3{Tg00YEj2NTg00<Kj2>Tg004Rj2VTg004lj4TTg005Gj3hTg005dj1uTg006kj3tTg007Hj1sTg00ZPj2rTg00`ij2qTg00b0j2gTg018oj3pTg01:=j6vTg0042j36Tg00dBj3UTg00\Yj4oTf0R0#0#0#0#1p=8%00#0#1#1p=Z%10#0#0#1p=:%00#1#1#0p=i%00#0#0#9p=3%10#0p=Q%00#0#1#0p=I%10#0#1#1p=Y%10#1#0#0p=F%90#Mp=G%00#0p=S%00#1#0#0p=7%10#1#1#0p=<%00#1p=c%20#2p=a%20#2#2#2p=@%10#0#0#0p==%00#0#0#0#0#0#0#0p=D%00#1#1#1p=5%10#0#1#0p=Kg00fMR1f2R2#Bf1R3#B=61036p=JA61309612p=R%B3=610p=\%00#0#0#0p=;%00#]p=ff3R4/A2?U30p=e%10#1#1#1p=4%]0,A3p=}%10#1p=l%00#1#0#0#0p=H%00#0#1p=X%00#1#0p=W%93/N0p=zg00@`R5A6530762p=P%02#9/N3=650p=EAU423=650p=k1N23=650p=y%03#9,N2=650p=jf6f5f4R63UAU423=650565p=x1N641N23=650565p=w%]4,A6?U23=650p=LP1P3g01;BR3P0Cop=`g00eMR2g00emR67C0p=bg00<fR0g00=DR4#dR7'OR8/O2R9P8P2P0P7g00?\R:#0#8#Z#:#i#3%_4C?P6C?R4;C41O11R;/O1R</O1R=P<P1P;P1P1P1%Q:#I#Y#:#F#GR>g00ihR?g00AkR@#2RA#2RB#2RC#2RD#2RE#2RF#BRG%2FRF#BRH3^RIC?%S:#7#<#:#c#:#9RJ#MRKC?%2FRF#aRL#2RM#2RN#2#@#@#@#@#@RO#2RP#2RQ#2RR#a#@RS#BRTC?RU;CURVAC266RW%d1RX%2SRS%B@RY%0:RZ#0R[#0R\#0R]#0R^#0R_#0R`#]#M5^?%=]#D#G%0:#7#5#K#7#3Ra#M%2S#@Rb%2bRb%2bRb%GZRc%@bRb#B%2bRb%2bRb%2bRb%2bRb%2bRb%2bRb%1:Rd#G%2b#a#@#@Rb%2bRb%2bRb%2b%_13J3J9JQR9JOP9RKT,\F5RH,\B3J3J3J5RI7RG'\3J3R5R>'\R>;C>RI%d5RH%9:RK%0`#;R`#;RP#9RO5[TPY%1\#SRT#fPF%Q:#I#F#;#7#GCe%9]R],nY%1dRR#1RQ#4#4#4Rb#;#D#D#D#3%0P#S#;RP#0#;#D#D#35[Y1}YPRe%9PRP'mPY%SQ#fPFg00k@RQ#MRfCePY%0R#SRR#0PFPfPY%0dRd#=PFPfPY%;dPFPfPY%1ZRZ#=PF%G^9^?YPY%;ZPF%Q:#I#Y#8#F#GPY%=[PFPcPYP_PF%G\R\9^?YPYPRPF%1:#l#:#K#5#F#G%H:#K#D#3RR%lb#4Rb#Q#4#<#;#D#35[G1nG]PePP1AGQPOC|%1T#Q#D#3RT,Af%Q:#7#D#3'm%0:#I#5#c#;#=%8:#Z#K#8#8#9PJ%S:#=#<#:#c#:#9%0:#7#5#=#K#3%X:#8#<#:#F%H:#5#K#:#3%0:#7#5#=#Y#3RJ,AfPF%MJ%0:#7#5#=#4#3,AfPD%BERE%X:#8#<#7#I%0:#7#5#:#K#3%X:#8#<#i#F%0:#7#5#:#<#3%X:#8#<#5#F%0:#7#5#K#I#3%X:#8#<#:#=%W:#8#<#Y#;%H:#5#4#I#3RD1AfD?{\B%7:#Z#4#:#=%H:#5#4#7#3'z%7:#Z#4#Y#8#9%H:#5#4#5#3R\1Af\PF%BC%W:#8#4#<#;%H:#5#4#:#3%W:#8#4#<#F%H:#5#4#F#3RC1AfCPF%9`R`#M%W:#8#4#4#7%H:#=#;#Z#3%W:#I#8#4#;%9b9[EK1NQ`%_53P7ER3ECk3E3ECk3y3P3E5ja3E3E3EFx3EDw5jO3P3PDLDLDLDLDLDLDLDL3P3P3PRO;CORa/>WRR'>R5,>WR`'>RE'>1V94PVPE1V=UPWP`1V26R6PWP5P6PIPR1VX>PaPW1VHOP6CTCTCTCTCTCTP8P2P0P7g00BJR21O27g00CXg01<A3hR87h7R6#uAt278C?%s6,r@C?=C94P<P1P;P1P1P11`Af1`LfC?1`MfC?1`NfC?=C=U1qS3#bg01=?RU,gS#bg01>>=p3Sg01??5CX1O00#_PQPQg01@?PTPUEvg01A<RU5CH1gSU#b'>'>'>'>'>'>do"). Qed.

Lemma l_itinD :
  (s_pc (fst (fst l_rDn)), snd (fst l_rDn), s_log (fst (fst l_rDn)))
    = (0x62be8%Z, [SCBr false BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ (s_pc (fst (fst l_rDt)), snd (fst l_rDt), s_log (fst (fst l_rDt)))
    = (0x62bb0%Z, [SCBr true BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ kn_after l_rDt l_knD0 = l_knD
  /\ (sr_mismatch d_rvl idb l_srDn sr_L 0, kn_missing l_knD (map (kmap d_rvl idb) kn_ML))
     = ([0%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ (sr_mismatch f_rvl idb l_srDt sr_F 0, kn_missing l_knD (map (kmap f_rvl idb) kn_ML))
     = ([0%nat; 19%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ nth 19 l_srDt (ELit 0) = EAlu ALU_ADD (EVar 7) (EVar 42).
Proof.
ltac2:(KReplay.run1 (kr_t_O23ReadLoop_defs ()) ["VP1"] "p;1p;2p;3p;4p;5g0000j1[Tg000Pj2UTg0010j11Tg00M=j19Tg00M\j1JTg00Onj3^Tg00Q7j4oTg002Xj1\Tg0042j37Tg0038j4;Tg003Xj3<Tg002:j15Tg001Uj10Tg00SOj3]Tg00L4j1CTg00RDj2dTg00TZj2_Tg00Uej2?Tg00Voj4{Tg00X:j3zTg00YEj2LTg00<Kj2DTg004Rj2OTg004lj4QTg005Gj3YTg005dj1kTg006kj3jTg007Hj1gTg00[Wj2sTg008Pj5iTg009]j2nTg00;?j2lTg00\Yj4rTg00KVj1bTg00dBj3RTg00:cj4qTf0R0#0#0#0#1p=4%00#1#0#1p=T%10#1#1#1p=3%00#1p=X%00#0#0#5p=2%90#9p=a%90#9#9#9p=I%00#0p=N%00#1#1#1p=6%00#1#1#0p=W%00#0#0#0p=8%00#bp=f%00#0#1#0p=G%00#5p=`f3R1f2R2'?f1R3;R0p=e%00#0#0#0#0#0#0#0p=B%b0,?3p=p%10#0#0#0p=E%10#1#1#0p=:%00#0#1#1p=K%00#1#0#0#0p=A%10#0#1#0p=@%10#1p=V%10#0p=c%00#1#0#0p==%10#0#0#1p=F%00#0#1p=P%10#1#0#0p=S%53/L0p=y%00#1#0p=Zg00@`R4A7430772p=M%02#5/L3=740p=>AR123=740p=m1L23=740p=xf6f5f4R53RAR123=740574p=w1L511L23=740574p=v%03#5,L2=740p=u%b1,?5?R23=740p=HA7430p=tP4P4P0g00JWCqp=hg00<fR0g00=DR3#[R2'UR5g00>QR1#[R6'UR7P5P6P0P2g00?\R8#1#4#T#3#X#2g00hVg01B<R9g00ihR:g00AkR;#aR<#9R=#9R>#9R?#9R@#9RA#J%9ARA#9#a#I#IRB#9#a#I#I#I#I#I#JRC3^RD%JARECo%\3RF573C;%\1R1C;RG;<GP5P6P0P2%18#N#T#6#W#2g00emP9PDPECo=73FC;P1C;R1=<71RF%[4R3%58RE%08R9#0RH#0RI#0RJ#0RK#0RL#N#8RM#8RN#5RO5]C%J;RC%1I#NRP#fPA%18#4#W#8#G#`#CCe%5JRJ,dC%18RQ#1RR#1RS#3#3#3RT#8#B#B#B#2%0N#N#8RN#0#8#B#B#25]C1pCNRU%5NRN'_PC%NS#fPAg00k@RS#CRVCePC%0R#NRR#0PAPVPC%0QRQ#EPAPVPC%8QPAPVPC%19RQ#EPA%5K#C9^:CPC%8QPA%18#4#T#E#:#`#CPC%EHPA%59#CPCPLPA%5I#CRI9^:CPCPRPA%38#K#X#K#:#`#C%J@R@%A8#@#B#2RR%VT#3RT#c#3#:#8#B#23]1d@JPUPN1?@SR@POC{%1P#c#B#2,?V%c8#=#B#2'_%08#G#6#X#8#E%48#K#@#4#4#5%48#K#@#T#F#5%G8#K#@#T#F#5%08#=#6#E#@#2%P8#4#:#F#S%A8#6#@#F#2%P8#4#:#G#V#2RP,?VPA%CP%08#=#6#E#3#2,?VP>%J?R?%P8#4#:#=#G%08#=#6#F#@#2%P8#4#:#W#S%08#=#6#F#:#2%P8#4#:#6#S%08#=#6#@#G#2%P8#4#:#F#8%08#=#6#@#W#2%A8#6#@#V#8%A8#6#3#G#2R>1?V>?zI<%=8#K#3#F#E%A8#6#3#=#2'y%X8#8#3#:#V#4#5%A8#6#3#6#2RI1?VIPA%J=%Z8#4#3#:#8%A8#6#3#F#2%Z8#4#3#:#S%A8#6#3#S#2R=1?V=PA%5MRM#C%Z8#4#3#3#=%A8#E#8#K#2%Z8#G#4#3#8%5T9]?E1LSM%\4R43M7>R3>Cm3>3>Cm3x3M3>3>3>3>3>Fw3>Dv5uO3M3MDHDHDHDHDHDHDHDH3M3M3MRR;<RRMg00@ARS#[R?/U3REP?P3%\SRT97S;1_@O/t4R4C;R@;<@ROP?P3A7SBT97S;P4C;R4=<E4RSg00fMRT?<DDR8'DRA'DR='DRI'D1O7GPFPI1O71PMP=1O3RPOPA1OE@PSP81OE41OTDCQCQCQCQCQP5P6P0P2g00BJR81U82RSg00CXRAg01Bn3YRO7Y2RR#kAj82OC;%gRC;=<7GP5P6P0P2g01CmR09YSARA9Y82RS#kAj82AC;%gSC;=<71g01A<,s0g01DlR05<3P?P3g01EkR1g00F`R7g01Fjg00H[P;Di1n17#h,l0C;=<E@P?P3g01GjR3P7g01HiR?g01IiP;Di1n37#h,l0C;=<E4PTPBP?PVCr=<TD'D'D'D'D'Ddo"). Qed.
End VP1.
