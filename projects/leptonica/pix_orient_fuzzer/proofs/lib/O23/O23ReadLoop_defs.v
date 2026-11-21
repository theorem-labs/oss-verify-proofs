(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's stack window: 6144513 writable bytes below the entry stack pointer instead of 8 MiB; the recorded proofs of l_itinA, l_itinB and l_itinD, made over the old 8 MiB launch stack window, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped). *)
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
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-6144513)) 6144513;
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
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP1.
