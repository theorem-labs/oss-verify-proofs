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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2OpenFail_defs V2Open_defs V2Oom_defs V2DirRead_defs V2ReadLoop_defs.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Hdr_defs () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4cfgFC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4zseqC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall9log_win_bC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingK47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4h_rSC5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness?AgentSubmission2V2:V2RelocImg7v2_datac5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_srSc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_knSc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_scSc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_rS2c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6f_rvlSC5ARocqVerifyHarness?AgentSubmission2V2?V2ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6h_srS2c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5sr_F2c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6h_knS2c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5kn_F2K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes4bool02c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4h_rOc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs8cfglen_xc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_srOc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_knOc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_scOc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_rO2c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6f_rvlOc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6h_srO2c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6h_knO2C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC5ARocqVerifyHarness?AgentSubmission2V2:V2Oom_defs8kn_acallC47Corelib5Lists7ListDef3nthc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5f_sr1c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5f_sr2I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4f_r1c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5f_kn1c5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs6f_kn2ic5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4f_r2C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26s_nextc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4h_rKc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs8paylen_xc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5pay_xc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5r_rvlc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_srKc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4sr_Rc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs5h_knKc5ARocqVerifyHarness?AgentSubmission2V2:V2Hdr_defs4kn_R".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSH : list Z := (0x17b38 :: STOPSL)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH scr ss [].
Definition STOPSH2 : list Z := (0x17a5c :: STOPSH)%Z.
Definition runH2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH2 scr ss [].

(* [comment removed for export] *)
Definition kn_H6 : list kentry :=
  KWord (SA (EVar 6) 0) 1 (EVar 41) :: KWord (SA (EVar 6) 1) 1 (EVar 42) :: KWord (SA (EVar 6) 2) 1 (EVar 43)
  :: KRange (EVar 41) 0 255 :: KRange (EVar 42) 0 255 :: KRange (EVar 43) 0 255 :: kn_ML.

(* [comment removed for export] *)
Definition h_rS := Eval vm_compute in runH (SCR [true] [] []) (SS 0x17964 sr_H [] kn_ML 41).
Definition h_srS : list expr := Eval vm_compute in s_regs (fst (fst h_rS)).
Definition h_knS : list kentry := Eval vm_compute in kn_after h_rS kn_ML.
Definition h_scS : stdio_res := Eval vm_compute in sc_of 41 h_srS h_knS.
(* [comment removed for export] *)
Definition h_srS2i : list expr := Eval vm_compute in sc_sr h_scS.
Definition h_knS2i : list kentry := Eval vm_compute in sc_kn h_scS.
Definition h_rS2 := Eval vm_compute in runH2 scr0 (SS 0x3e818 h_srS2i [] h_knS2i 73).
Definition h_srS2 : list expr := Eval vm_compute in s_regs (fst (fst h_rS2)).
Definition h_knS2 : list kentry := Eval vm_compute in kn_after h_rS2 h_knS2i.

(* [comment removed for export] *)
Definition h_rK := Eval vm_compute in runH (SCR [false; false] [] []) (SS 0x17964 sr_H [] kn_H6 44).
Definition h_srK : list expr := Eval vm_compute in s_regs (fst (fst h_rK)).
Definition h_knK : list kentry := Eval vm_compute in kn_after h_rK kn_H6.

Definition cfglen_x : expr := Eval vm_compute in nth 18 h_srK (ELit 0).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_rO := Eval vm_compute in runH (SCR [false; true] [] []) (SS 0x17964 sr_H [] kn_H6 44).
Definition h_srO : list expr := Eval vm_compute in s_regs (fst (fst h_rO)).
Definition h_knO : list kentry := Eval vm_compute in kn_after h_rO kn_H6.
Definition h_scO : stdio_res := Eval vm_compute in sc_of 44 h_srO h_knO.
Definition h_srO2i : list expr := Eval vm_compute in sc_sr h_scO.
Definition h_knO2i : list kentry := Eval vm_compute in sc_kn h_scO.
Definition h_rO2 := Eval vm_compute in runH2 scr0 (SS 0x3e818 h_srO2i [] h_knO2i 76).
Definition h_srO2 : list expr := Eval vm_compute in s_regs (fst (fst h_rO2)).
Definition h_knO2 : list kentry := Eval vm_compute in kn_after h_rO2 h_knO2i.

(* [comment removed for export] *)
Definition JF (i : nat) : expr := EVar (7 + i).
Definition sr_F2 : list expr :=
  [ELit 0; JF 1; spx (-128); ELit 0x10800; ELit 0x56270; JF 5; JF 6; JF 7;
   ELit 2; EVar 6; JF 10; JF 11; JF 12; JF 13; JF 14; JF 15;
   JF 16; JF 17; JF 18; JF 19; JF 20; JF 21; JF 22; JF 23;
   JF 24; JF 25; JF 26; JF 27; JF 28; JF 29; JF 30; JF 31].
Definition kn_F2 : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) h_knO2.
Definition f_rvlS : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srS2).
Definition f_rvlO : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srO2).
(* [comment removed for export] *)
Definition f_r1 := Eval vm_compute in runH scr0 (SS 0x17a5c sr_F2 [] kn_F2 39).
Definition f_sr1 : list expr := Eval vm_compute in s_regs (fst (fst f_r1)).
Definition f_kn1 : list kentry := Eval vm_compute in kn_after f_r1 kn_F2.
(* [comment removed for export] *)
Definition f_sr2i : list expr := Eval vm_compute in sr_after_call_j f_sr1 KEPT_AL 39.
Definition f_kn2i : list kentry := Eval vm_compute in kn_acall f_kn1.
Definition f_r2 := Eval vm_compute in runH scr0 (SS 0x17a64 f_sr2i [] f_kn2i 71).
Definition f_sr2 : list expr := Eval vm_compute in s_regs (fst (fst f_r2)).
Definition f_kn2 : list kentry := Eval vm_compute in kn_after f_r2 f_kn2i.

Definition paylen_x : expr := Eval vm_compute in nth 13 h_srK (ELit 0).    (* [comment removed for export] *)
Definition pay_x : expr := Eval vm_compute in nth 12 h_srK (ELit 0).       (* [comment removed for export] *)
Definition b1s_x : expr := EExt true 0 1 (EVar 42).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JR (i : nat) : expr := EVar (13 + i).
Definition sr_R : list expr :=
  [ELit 0; ELit 0x179dc; spx (-128); ELit 0x10800; ELit 0x56270; JR 5; JR 6; JR 7;
   EAlu ALU_ADD (EVar 6) (ELit 2); EVar 6; EAlu ALU_ADD (EVar 6) (ELit 2); EVar 8; EVar 12; EVar 9; JR 14; JR 15;
   JR 16; JR 17; EVar 8; EVar 12; EVar 9; EVar 10; JR 22; JR 23;
   JR 24; JR 25; JR 26; JR 27; JR 28; JR 29; JR 30; JR 31].
Definition kn_R : list kentry := KWord (SA (EVar 6) 2) 1 (EVar 11) :: KRange (EVar 11) 0 255 :: kn_ML.
Definition NXR : nat := 45.
Definition r_rvl : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; cfglen_x; paylen_x; b1s_x; EVar 43; pay_x] ++ (ELit 0 :: tl h_srK).

(* [comment removed for export] *)
Definition cfgF (v41 v42 : word) : word :=
  edenot (Env (fun n => match n with 41%nat => v41 | 42%nat => v42 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfglen_x.
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma cfgF_tab :
  forallb (fun b1 => forallb (fun b0 =>
     Z.eqb (bv_unsigned (cfgF (Z_to_bv 64 b0) (Z_to_bv 64 b1))) ((b0 + 256 * b1) mod 32768))
     (zseq 256)) (zseq 256) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Hdr_defs ()) [] "h02b0h12b1p;2p;1p;3g0000j2@Tg000Jj1;Tg000hj24Tg001Nj2?Tg002Ej2<Tg002oj15Tg003Mj2:Tg003jj29Tg004Gj13Tg004lj27Tg005Lj28Tg005ij1>Tg006`j36Tg007<j3=Tg007Vj10Tf0R0#3#3p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g0085R1g008UR2'@g0095R3g009S#2#2#2R4#;R51450f1R6,45'?'<%24R4#5/:6,90%34#2#2#2#5'7'8X03g00:8#1#1#1#1#1#1#1#1#>R4563X13;64==12do"). Qed.   (* [comment removed for export] *)

Section VP1.
Lemma h_itinS :
  (s_pc (fst (fst h_rS)), snd (fst h_rS)) = (0x3e37c%Z, [SCBr true BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 41 h_srS h_knS = Some h_scS
  /\ (sc_ret h_scS, sc_f h_scS, sc_fd h_scS, sc_s h_scS, sc_l h_scS) = (0x3e818%Z, 0x45f30%Z, 2%Z, ELit 0x121e7, ELit 31)
  /\ (s_pc (fst (fst h_rS2)), snd (fst h_rS2), log_win_b 0 (s_log (fst (fst h_rS2)))) = (0x17a5c%Z, [], true)
  /\ (sr_mismatch f_rvlS idb h_srS2 sr_F2 0, kn_missing h_knS2 (map (kmap f_rvlS idb) kn_F2)) = ([0%nat], []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma h_itinO :
  (s_pc (fst (fst h_rO)), snd (fst h_rO)) = (0x3e37c%Z, [SCBr true BC_LTU (EVar 7) (EAlu ALU_ADD cfglen_x (ELit 6)); SCBr false BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 44 h_srO h_knO = Some h_scO
  /\ (sc_ret h_scO, sc_f h_scO, sc_fd h_scO, sc_s h_scO, sc_l h_scO) = (0x3e818%Z, 0x45f30%Z, 2%Z, ELit 0x10bfc, ELit 31)
  /\ (s_pc (fst (fst h_rO2)), snd (fst h_rO2), log_win_b 0 (s_log (fst (fst h_rO2)))) = (0x17a5c%Z, [], true)
  /\ (sr_mismatch f_rvlO idb h_srO2 sr_F2 0, kn_missing h_knO2 (map (kmap f_rvlO idb) kn_F2)) = ([0%nat], []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma f_itin :
  (s_pc (fst (fst f_r1)), snd (fst f_r1), s_log (fst (fst f_r1))) = (0x3c230%Z, [], [])
  /\ (nth 1 f_sr1 (ELit 0), nth 10 f_sr1 (ELit 0), nth 2 f_sr1 (ELit 0), nth 4 f_sr1 (ELit 0))
     = (ELit 0x17a64, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x56270)
  /\ kn_vars_lt 39 f_kn1 = true /\ kn_acall f_kn1 = f_kn2i
  /\ (s_pc (fst (fst f_r2)), snd (fst f_r2), s_log (fst (fst f_r2))) = (0x3bef8%Z, [], [])
  /\ (nth 10 f_sr2 (ELit 0), nth 2 f_sr2 (ELit 0), nth 4 f_sr2 (ELit 0)) = (ELit 2, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x56270).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.

Lemma h_itinK :
  (s_pc (fst (fst h_rK)), s_log (fst (fst h_rK)), s_next (fst (fst h_rK))) = (0x17b38%Z, [], 48%nat)
  /\ paylen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 7) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6))
  /\ pay_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 6) cfglen_x) (ELit 6)
  /\ (sr_mismatch r_rvl idb h_srK sr_R 0, kn_missing h_knK (map (kmap r_rvl idb) kn_R)) = ([], []).
Proof.
repeat match goal with |- _ /\ _ => split end; vm_compute; reflexivity.
Qed.
End VP1.
