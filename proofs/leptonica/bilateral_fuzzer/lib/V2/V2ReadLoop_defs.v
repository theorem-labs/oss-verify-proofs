(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2OpenFail_defs V2Open_defs V2Oom_defs V2DirRead_defs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2ReadLoop_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingI47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00K47Corelib4Init9Datatypes3nat01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs3e_rc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5e_rvlc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4e_src5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4sr_Lc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4e_knc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5kn_MLK47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall9log_win_bC5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs8kn_afterC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24ridxC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sr_updC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:sr_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver<LibKnowFrame8kn_frameK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_srAnK47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib7Numbers7BinNums1Z01c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_rAnc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6want_xc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_rAtc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_knAc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_srAtK47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_knRc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4l_rCc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_srCc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_rC2c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5h_rvlc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_srC2c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4sr_Hc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_knC2C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive?sr_after_call_jC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall7kn_callc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_srBc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4l_rBc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_knBC5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs7KEPT_MCc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_srD0C5ARocqVerifyHarness?AgentSubmission2V2?V2OpenFail_defs3IHIc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_knD0K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01c5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_rDnc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_rDtc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5l_knDc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5d_rvlc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_srDnc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs5f_rvlc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs6l_srDtc5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs4sr_F".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSL : list Z := (0x17934 :: 0x17964 :: 0x178fc :: STOPS3)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSL scr ss [].
Definition NXL : nat := 41.
Definition J (i : nat) : expr := EVar (9 + i).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_L : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x56270; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; ELit 3; EVar 8; ELit 0x46169; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_H : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x56270; J 5; J 6; J 7;
   ELit 2; EVar 6; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 7; J 20; J 21; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].
(* [comment removed for export] *)
Definition sr_F : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x56270; J 5; J 6; J 7;
   ELit 2; J 9; J 10; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 2; EVar 8; ELit 3; EVar 8; ELit 0x46169; EVar 6;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_ML : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000; KWr (SA (EVar 0) (-8388608)) 8388608;
   (* [comment removed for export] *)
   KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
   KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-88)) 8 (spx 32); KWord (SA (EVar 0) (-80)) 8 (ELit 0x17868);
   KWord (SA (EVar 0) (-72)) 8 (ELit 2); KWord (SA (EVar 0) (-64)) 8 (spx 8); KWord (SA (EVar 0) (-56)) 8 (ELit 0x3b9fc);
   (* [comment removed for export] *)
   KRange (EVar 6) 0x77000 0x7fffff7f0000; KAlign (EVar 6) 16; KWr (SA (EVar 6) 0) 65536;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 6) 0) 65536;
   (* [comment removed for export] *)
   KWr (SA (ELit 0) 0x45000) 204800;
   KImg 0x10000 0x46120; KImg 0x46121 0x46169; KImg 0x56169 0x561a0; KImg 0x56288 0x76298;
   KWord (SA (ELit 0) 0x561a8) 8 (ELit 0x561a8); KWord (SA (ELit 0) 0x561c8) 4 (EVar 5);
   KImg 0x561d4 0x56220; KImg 0x56228 0x56240; KImg 0x56248 0x56260; KImg 0x56270 0x56280; KImg 0x762b0 0x764d8;
   KBlob (SA (ELit 0) 0x764d8) (ELit 8) 2; KImg 0x764e0 0x764e8; KImg 0x764f9 0x76500;
   KWord (SA (ELit 0) 0x76500) 8 (EVar 3); KImg 0x76508 0x76510; KImg 0x76520 0x76528;
   KWord (SA (ELit 0) 0x76528) 8 (ELit 4096); KImg 0x76530 0x76560; KImg 0x76918 0x77000;
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
Definition l_ssA : sym_state := SS 0x17934 sr_L [] kn_ML NXL.
Definition l_rAn := Eval vm_compute in runL (SCR [false] [] []) l_ssA.   (* [comment removed for export] *)
Definition l_rAt := Eval vm_compute in runL (SCR [true] [] []) l_ssA.    (* [comment removed for export] *)
Definition l_srAn : list expr := Eval vm_compute in s_regs (fst (fst l_rAn)).
Definition l_srAt : list expr := Eval vm_compute in s_regs (fst (fst l_rAt)).
Definition l_knA : list kentry := Eval vm_compute in kn_after l_rAn kn_ML.
(* [comment removed for export] *)
Definition l_srR (e : expr) : list expr := sr_upd (sr_upd l_srAn (ridx 12) (EVar 41)) (ridx 10) e.
Definition l_knR : list kentry := Eval vm_compute in kn_frame l_knA (ELit 0) 0x46169 65536.

(* [comment removed for export] *)
Definition l_rC := Eval vm_compute in runL scr0 (SS 0x43d68 (l_srR (ELit 0)) [] l_knR 42).
Definition l_srC : list expr := Eval vm_compute in s_regs (fst (fst l_rC)).
Definition l_knC : list kentry := Eval vm_compute in kn_after l_rC l_knR.
Definition l_rC2 := Eval vm_compute in runL scr0 (SS 0x43d68 (sr_upd l_srC (ridx 10) (ELit 0)) [] l_knC 42).
Definition l_srC2 : list expr := Eval vm_compute in s_regs (fst (fst l_rC2)).
Definition l_knC2 : list kentry := Eval vm_compute in kn_after l_rC2 l_knC.
Definition h_rvl : list expr := rvl9 (EVar 6) (EVar 7) (EVar 8) l_srC2.

(* [comment removed for export] *)
Definition l_knRB : list kentry := KRange (EVar 42) 1 65536 :: l_knR.
Definition l_rB := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x43d68 (l_srR (EVar 42)) [] l_knRB 43).
Definition l_srB : list expr := Eval vm_compute in s_regs (fst (fst l_rB)).
Definition l_knB : list kentry := Eval vm_compute in kn_after l_rB l_knRB.

(* [comment removed for export] *)
Definition l_srD0 : list expr := Eval vm_compute in sr_after_call_j l_srB KEPT_MC 43.
Definition l_knD0 : list kentry := Eval vm_compute in kn_call [] 0 0 IHI 0x45000 l_knB.
Definition l_rDn := Eval vm_compute in runL (SCR [false] [] []) (SS 0x178e8 l_srD0 [] l_knD0 75).  (* [comment removed for export] *)
Definition l_rDt := Eval vm_compute in runL (SCR [true] [] []) (SS 0x178e8 l_srD0 [] l_knD0 75).   (* [comment removed for export] *)
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
  (s_pc (fst (fst e_r)), snd (fst e_r), s_log (fst (fst e_r))) = (0x17934%Z, [], [])
  /\ (sr_mismatch e_rvl idb e_sr sr_L 0, kn_missing e_kn (map (kmap e_rvl idb) kn_ML)) = ([0%nat], []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma l_itinA :
  (s_pc (fst (fst l_rAn)), snd (fst l_rAn), log_win_b 0 (s_log (fst (fst l_rAn))))
    = (0x43d64%Z, [SCBr false BC_LTU want_x (ELit 65536)], true)
  /\ (s_pc (fst (fst l_rAt)), snd (fst l_rAt), log_win_b 0 (s_log (fst (fst l_rAt))))
    = (0x43d64%Z, [SCBr true BC_LTU want_x (ELit 65536)], true)
  /\ kn_after l_rAt kn_ML = l_knA
  /\ (nth 17 l_srAn (ELit 0), nth 10 l_srAn (ELit 0), nth 11 l_srAn (ELit 0), nth 12 l_srAn (ELit 0))
     = (ELit 63, ELit 3, ELit 0x46169, ELit 65536)
  /\ nth 12 l_srAt (ELit 0) = want_x
  /\ sr_upd l_srAt (ridx 12) (EVar 41) = sr_upd l_srAn (ridx 12) (EVar 41)
  /\ sr_vars_lt 41 l_srAn = true /\ sr_vars_lt 41 l_srAt = true /\ kn_vars_lt 41 l_knA = true
  /\ kn_frame l_knA (ELit 0) 0x46169 65536 = l_knR
  /\ sr_vars_lt 42 (sr_upd l_srAn (ridx 12) (EVar 41)) = true /\ kn_vars_lt 42 l_knR = true.
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma l_itinC :
  (s_pc (fst (fst l_rC)), snd (fst l_rC), log_win_b 0 (s_log (fst (fst l_rC))), nth 17 l_srC (ELit 0), nth 10 l_srC (ELit 0))
    = (0x43d64%Z, [], true, ELit 57, ELit 3)
  /\ (s_pc (fst (fst l_rC2)), snd (fst l_rC2), s_log (fst (fst l_rC2))) = (0x17964%Z, [], [])
  /\ (sr_mismatch h_rvl idb l_srC2 sr_H 0, kn_missing l_knC2 (map (kmap h_rvl idb) kn_ML)) = ([], []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma l_itinB :
  (s_pc (fst (fst l_rB)), snd (fst l_rB), log_win_b 0 (s_log (fst (fst l_rB)))) = (0x4347c%Z, [], true)
  /\ (nth 1 l_srB (ELit 0), nth 10 l_srB (ELit 0), nth 11 l_srB (ELit 0), nth 12 l_srB (ELit 0))
     = (ELit 0x178e8, EAlu ALU_ADD (EVar 6) (EVar 7), ELit 0x46169, EVar 42)
  /\ sr_vars_lt 43 l_srB = true /\ kn_vars_lt 43 l_knB = true
  /\ sr_after_call_j l_srB KEPT_MC 43 = l_srD0 /\ kn_call [] 0 0 IHI 0x45000 l_knB = l_knD0 /\ kn_vars_lt 43 l_knD0 = true.
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma l_itinD :
  (s_pc (fst (fst l_rDn)), snd (fst l_rDn), s_log (fst (fst l_rDn)))
    = (0x17934%Z, [SCBr false BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ (s_pc (fst (fst l_rDt)), snd (fst l_rDt), s_log (fst (fst l_rDt)))
    = (0x178fc%Z, [SCBr true BC_EQ (EAlu ALU_ADD (EVar 7) (EVar 42)) (EVar 8)], [])
  /\ kn_after l_rDt l_knD0 = l_knD
  /\ (sr_mismatch d_rvl idb l_srDn sr_L 0, kn_missing l_knD (map (kmap d_rvl idb) kn_ML))
     = ([0%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ (sr_mismatch f_rvl idb l_srDt sr_F 0, kn_missing l_knD (map (kmap f_rvl idb) kn_ML))
     = ([0%nat; 19%nat], [KWr (SA (EVar 6) 0) 65536])
  /\ nth 19 l_srDt (ELit 0) = EAlu ALU_ADD (EVar 7) (EVar 42).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP1.
