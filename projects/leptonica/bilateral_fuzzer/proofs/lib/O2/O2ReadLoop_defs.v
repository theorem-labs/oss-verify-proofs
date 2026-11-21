(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (addresses and constants; recorded (KReplay) proofs re-proved by tactics, as pix_orient_fuzzer's copy). *)
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
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-6144513)) 6144513;
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
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
