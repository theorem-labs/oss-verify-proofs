(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of h_itinS, h_itinO and f_itin, made over the old 8 MiB launch stack window, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped). *)
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
Ltac2 kr_t_O23Hdr_defs () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib3O23;O23Hdr_defs4cfgFC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbc59OSSVerify5KrLib3O23;O23Hdr_defs4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs4h_rSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_srSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_knSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_scSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_rS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6f_rvlSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6h_srS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5sr_F2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6h_knS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5kn_F2C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib3O23;O23Hdr_defs4h_rOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs8cfglen_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_srOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_knOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_scOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_rO2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6f_rvlOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6h_srO2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6h_knO2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib3O23;O23Hdr_defs5f_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5f_sr2C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs4f_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5f_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs6f_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs4f_r2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs4h_rKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs8paylen_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5pay_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5r_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_srKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs4sr_RC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs5h_knKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23;O23Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPSH : list Z := (0x62dec :: STOPSL)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH scr ss [].
Definition STOPSH2 : list Z := (0x62d10 :: STOPSH)%Z.
Definition runH2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH2 scr ss [].

(* [comment removed for export] *)
Definition kn_H6 : list kentry :=
  KWord (SA (EVar 6) 0) 1 (EVar 41) :: KWord (SA (EVar 6) 1) 1 (EVar 42) :: KWord (SA (EVar 6) 2) 1 (EVar 43)
  :: KRange (EVar 41) 0 255 :: KRange (EVar 42) 0 255 :: KRange (EVar 43) 0 255 :: kn_ML.

(* [comment removed for export] *)
Definition h_rS := Eval vm_compute in runH (SCR [true] [] []) (SS 0x62c18 sr_H [] kn_ML 41).
Definition h_srS : list expr := Eval vm_compute in s_regs (fst (fst h_rS)).
Definition h_knS : list kentry := Eval vm_compute in kn_after h_rS kn_ML.
Definition h_scS : stdio_res := Eval vm_compute in sc_of 41 h_srS h_knS.
(* [comment removed for export] *)
Definition h_srS2i : list expr := Eval vm_compute in sc_sr h_scS.
Definition h_knS2i : list kentry := Eval vm_compute in sc_kn h_scS.
Definition h_rS2 := Eval vm_compute in runH2 scr0 (SS 0xfffdc h_srS2i [] h_knS2i 73).
Definition h_srS2 : list expr := Eval vm_compute in s_regs (fst (fst h_rS2)).
Definition h_knS2 : list kentry := Eval vm_compute in kn_after h_rS2 h_knS2i.

(* [comment removed for export] *)
Definition h_rK := Eval vm_compute in runH (SCR [false; false] [] []) (SS 0x62c18 sr_H [] kn_H6 44).
Definition h_srK : list expr := Eval vm_compute in s_regs (fst (fst h_rK)).
Definition h_knK : list kentry := Eval vm_compute in kn_after h_rK kn_H6.

Definition cfglen_x : expr := Eval vm_compute in nth 18 h_srK (ELit 0).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_rO := Eval vm_compute in runH (SCR [false; true] [] []) (SS 0x62c18 sr_H [] kn_H6 44).
Definition h_srO : list expr := Eval vm_compute in s_regs (fst (fst h_rO)).
Definition h_knO : list kentry := Eval vm_compute in kn_after h_rO kn_H6.
Definition h_scO : stdio_res := Eval vm_compute in sc_of 44 h_srO h_knO.
Definition h_srO2i : list expr := Eval vm_compute in sc_sr h_scO.
Definition h_knO2i : list kentry := Eval vm_compute in sc_kn h_scO.
Definition h_rO2 := Eval vm_compute in runH2 scr0 (SS 0xfffdc h_srO2i [] h_knO2i 76).
Definition h_srO2 : list expr := Eval vm_compute in s_regs (fst (fst h_rO2)).
Definition h_knO2 : list kentry := Eval vm_compute in kn_after h_rO2 h_knO2i.

(* [comment removed for export] *)
Definition JF (i : nat) : expr := EVar (7 + i).
Definition sr_F2 : list expr :=
  [ELit 0; JF 1; spx (-128); ELit 0x10800; ELit 0x123d20; JF 5; JF 6; JF 7;
   ELit 2; EVar 6; JF 10; JF 11; JF 12; JF 13; JF 14; JF 15;
   JF 16; JF 17; JF 18; JF 19; JF 20; JF 21; JF 22; JF 23;
   JF 24; JF 25; JF 26; JF 27; JF 28; JF 29; JF 30; JF 31].
Definition kn_F2 : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) h_knO2.
Definition f_rvlS : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srS2).
Definition f_rvlO : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srO2).
(* [comment removed for export] *)
Definition f_r1 := Eval vm_compute in runH scr0 (SS 0x62d10 sr_F2 [] kn_F2 39).
Definition f_sr1 : list expr := Eval vm_compute in s_regs (fst (fst f_r1)).
Definition f_kn1 : list kentry := Eval vm_compute in kn_after f_r1 kn_F2.
(* [comment removed for export] *)
Definition f_sr2i : list expr := Eval vm_compute in sr_after_call_j f_sr1 KEPT_AL 39.
Definition f_kn2i : list kentry := Eval vm_compute in kn_acall f_kn1.
Definition f_r2 := Eval vm_compute in runH scr0 (SS 0x62d18 f_sr2i [] f_kn2i 71).
Definition f_sr2 : list expr := Eval vm_compute in s_regs (fst (fst f_r2)).
Definition f_kn2 : list kentry := Eval vm_compute in kn_after f_r2 f_kn2i.

Definition paylen_x : expr := Eval vm_compute in nth 13 h_srK (ELit 0).    (* [comment removed for export] *)
Definition pay_x : expr := Eval vm_compute in nth 12 h_srK (ELit 0).       (* [comment removed for export] *)
Definition b1s_x : expr := EExt true 0 1 (EVar 42).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JR (i : nat) : expr := EVar (13 + i).
Definition sr_R : list expr :=
  [ELit 0; ELit 0x62c90; spx (-128); ELit 0x10800; ELit 0x123d20; JR 5; JR 6; JR 7;
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
ltac2:(KReplay.run1 (kr_t_O23Hdr_defs ()) [] "h02b0h12b1p;2p;1p;3g0000j2@Tg000Jj1;Tg000hj24Tg001Nj2?Tg002Gj2<Tg0031j15Tg003Oj2:Tg003lj29Tg004Ij13Tg004nj27Tg005Nj28Tg005kj1>Tg006dj36Tg007@j3=Tg007Zj10Tf0R0#3#3p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g0089R1g008YR2'@g0099R3g009W#2#2#2R4#;R51450f1R6,45'?'<%24R4#5/:6,90%34#2#2#2#5'7'8X03g00:<#1#1#1#1#1#1#1#1#>R4563X13;64==12do"). Qed.   (* [comment removed for export] *)

Section VP1.
Lemma h_itinS :
  (s_pc (fst (fst h_rS)), snd (fst h_rS)) = (0xff528%Z, [SCBr true BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 41 h_srS h_knS = Some h_scS
  /\ (sc_ret h_scS, sc_f h_scS, sc_fd h_scS, sc_s h_scS, sc_l h_scS) = (0xfffdc%Z, 0x113808%Z, 2%Z, ELit 0x1d49f, ELit 31)
  /\ (s_pc (fst (fst h_rS2)), snd (fst h_rS2), log_win_b 0 (s_log (fst (fst h_rS2)))) = (0x62d10%Z, [], true)
  /\ (sr_mismatch f_rvlS idb h_srS2 sr_F2 0, kn_missing h_knS2 (map (kmap f_rvlS idb) kn_F2)) = ([0%nat], []).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma h_itinO :
  (s_pc (fst (fst h_rO)), snd (fst h_rO)) = (0xff528%Z, [SCBr true BC_LTU (EVar 7) (EAlu ALU_ADD cfglen_x (ELit 6)); SCBr false BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 44 h_srO h_knO = Some h_scO
  /\ (sc_ret h_scO, sc_f h_scO, sc_fd h_scO, sc_s h_scO, sc_l h_scO) = (0xfffdc%Z, 0x113808%Z, 2%Z, ELit 0x1436d, ELit 31)
  /\ (s_pc (fst (fst h_rO2)), snd (fst h_rO2), log_win_b 0 (s_log (fst (fst h_rO2)))) = (0x62d10%Z, [], true)
  /\ (sr_mismatch f_rvlO idb h_srO2 sr_F2 0, kn_missing h_knO2 (map (kmap f_rvlO idb) kn_F2)) = ([0%nat], []).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma f_itin :
  (s_pc (fst (fst f_r1)), snd (fst f_r1), s_log (fst (fst f_r1))) = (0xfa374%Z, [], [])
  /\ (nth 1 f_sr1 (ELit 0), nth 10 f_sr1 (ELit 0), nth 2 f_sr1 (ELit 0), nth 4 f_sr1 (ELit 0))
     = (ELit 0x62d18, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x123d20)
  /\ kn_vars_lt 39 f_kn1 = true /\ kn_acall f_kn1 = f_kn2i
  /\ (s_pc (fst (fst f_r2)), snd (fst f_r2), s_log (fst (fst f_r2))) = (0xfa03c%Z, [], [])
  /\ (nth 10 f_sr2 (ELit 0), nth 2 f_sr2 (ELit 0), nth 4 f_sr2 (ELit 0)) = (ELit 2, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x123d20).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma h_itinK :
  (s_pc (fst (fst h_rK)), s_log (fst (fst h_rK)), s_next (fst (fst h_rK))) = (0x62dec%Z, [], 48%nat)
  /\ paylen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 7) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6))
  /\ pay_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 6) cfglen_x) (ELit 6)
  /\ (sr_mismatch r_rvl idb h_srK sr_R 0, kn_missing h_knK (map (kmap r_rvl idb) kn_R)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g00:[j1<Tg00;;j2?Tg00;[j11Tg004Ij10Tg0031j1=Tg00>Vj1ATg00?Vj47Tg007Zj12Tg007@j34Tg00<@j1;Tg00\7j1GTg00@Xj19Tg013:j4FTg014Cj3BTg00Aaj3>Tg00Laj28Tg0000j2:Tg00M<j4@Tg00MWj3ETg00N4j1NTg00Umj1MTg01J7j1LTg00X<j5KTg00YIj2HTg00ZOj4ITg00Zkj2JTf0R0#0#0p=C%20#2#2#2p=3%20#2p=D%00#0#0#0#0#0#0#0p=6g00cZR1f1;>0p=5g0099R0g01EER2#<R3'?R4g00dFR5'?R6P4P5P0P3g009WR7#1#0#C#1#0#1#1#0#1#1#1#1#0#1#1#C#=%A2C7g00:<R2#2R8#2#3R9#2R:#D#3#3#3#3#3#3#3#3R;#2R<#D#3C7R=;4=g00]`R>%;:R:g017VR?%G7#9R@g016>g016j%07#6#6#6#6#6#6#6#=#9g008YP2P8%;<CF5B?%17#0R7#C#1#=#93>g018BP2P8%;;CF3>R;3B'5%G7#9R8'5R<;4<RA%;9R9/5;%=7#9R7'5R;=4>;RB%<5RCg00^iRD#<RE'?RFPCPE%A5%ADC7RG;4GRH'8RI'81:6=PAPI1:><PBPH1:>;1:FGC@C@C@P4P5P0P3g00deR3g00`4#<R01?30g00f3g01K@3E3ER0#N%M0C7%L0C7=46=g01L9g019[R=9B?@,5:/5854>g01M6A>19=/5754>PCPEg01N0REg00nSRCg01Njg01OdP2DKg01P]PDPD1HECg01QWCI'JC7=4FG'8'8'8do"). Qed.
End VP1.
