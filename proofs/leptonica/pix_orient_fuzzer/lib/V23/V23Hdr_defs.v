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
Ltac2 kr_t_V23Hdr_defs () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4cfgFC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4zseqC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall9log_win_bC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC47Corelib5Lists7ListDef3mapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingK47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4h_rSC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_datac5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_srSc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_knSc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_scSc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_rS2c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6f_rvlSC5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6h_srS2c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5sr_F2c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6h_knS2c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5kn_F2K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes4bool02c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4h_rOc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs8cfglen_xc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_srOc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_knOc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_scOc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_rO2c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6f_rvlOc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6h_srO2c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6h_knO2C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC5ARocqVerifyHarness?AgentSubmission3V23;V23Oom_defs8kn_acallC47Corelib5Lists7ListDef3nthc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5f_sr1c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5f_sr2I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4f_r1c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5f_kn1c5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs6f_kn2ic5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4f_r2C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26s_nextc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4h_rKc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs8paylen_xc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5pay_xc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5r_rvlc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_srKc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4sr_Rc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs5h_knKc5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4kn_R".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPSH : list Z := (0x63410 :: STOPSL)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH scr ss [].
Definition STOPSH2 : list Z := (0x63334 :: STOPSH)%Z.
Definition runH2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH2 scr ss [].

(* [comment removed for export] *)
Definition kn_H6 : list kentry :=
  KWord (SA (EVar 6) 0) 1 (EVar 41) :: KWord (SA (EVar 6) 1) 1 (EVar 42) :: KWord (SA (EVar 6) 2) 1 (EVar 43)
  :: KRange (EVar 41) 0 255 :: KRange (EVar 42) 0 255 :: KRange (EVar 43) 0 255 :: kn_ML.

(* [comment removed for export] *)
Definition h_rS := Eval vm_compute in runH (SCR [true] [] []) (SS 0x6323c sr_H [] kn_ML 41).
Definition h_srS : list expr := Eval vm_compute in s_regs (fst (fst h_rS)).
Definition h_knS : list kentry := Eval vm_compute in kn_after h_rS kn_ML.
Definition h_scS : stdio_res := Eval vm_compute in sc_of 41 h_srS h_knS.
(* [comment removed for export] *)
Definition h_srS2i : list expr := Eval vm_compute in sc_sr h_scS.
Definition h_knS2i : list kentry := Eval vm_compute in sc_kn h_scS.
Definition h_rS2 := Eval vm_compute in runH2 scr0 (SS 0x114480 h_srS2i [] h_knS2i 73).
Definition h_srS2 : list expr := Eval vm_compute in s_regs (fst (fst h_rS2)).
Definition h_knS2 : list kentry := Eval vm_compute in kn_after h_rS2 h_knS2i.

(* [comment removed for export] *)
Definition h_rK := Eval vm_compute in runH (SCR [false; false] [] []) (SS 0x6323c sr_H [] kn_H6 44).
Definition h_srK : list expr := Eval vm_compute in s_regs (fst (fst h_rK)).
Definition h_knK : list kentry := Eval vm_compute in kn_after h_rK kn_H6.

Definition cfglen_x : expr := Eval vm_compute in nth 18 h_srK (ELit 0).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_rO := Eval vm_compute in runH (SCR [false; true] [] []) (SS 0x6323c sr_H [] kn_H6 44).
Definition h_srO : list expr := Eval vm_compute in s_regs (fst (fst h_rO)).
Definition h_knO : list kentry := Eval vm_compute in kn_after h_rO kn_H6.
Definition h_scO : stdio_res := Eval vm_compute in sc_of 44 h_srO h_knO.
Definition h_srO2i : list expr := Eval vm_compute in sc_sr h_scO.
Definition h_knO2i : list kentry := Eval vm_compute in sc_kn h_scO.
Definition h_rO2 := Eval vm_compute in runH2 scr0 (SS 0x114480 h_srO2i [] h_knO2i 76).
Definition h_srO2 : list expr := Eval vm_compute in s_regs (fst (fst h_rO2)).
Definition h_knO2 : list kentry := Eval vm_compute in kn_after h_rO2 h_knO2i.

(* [comment removed for export] *)
Definition JF (i : nat) : expr := EVar (7 + i).
Definition sr_F2 : list expr :=
  [ELit 0; JF 1; spx (-128); ELit 0x10800; ELit 0x1381d0; JF 5; JF 6; JF 7;
   ELit 2; EVar 6; JF 10; JF 11; JF 12; JF 13; JF 14; JF 15;
   JF 16; JF 17; JF 18; JF 19; JF 20; JF 21; JF 22; JF 23;
   JF 24; JF 25; JF 26; JF 27; JF 28; JF 29; JF 30; JF 31].
Definition kn_F2 : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) h_knO2.
Definition f_rvlS : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srS2).
Definition f_rvlO : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srO2).
(* [comment removed for export] *)
Definition f_r1 := Eval vm_compute in runH scr0 (SS 0x63334 sr_F2 [] kn_F2 39).
Definition f_sr1 : list expr := Eval vm_compute in s_regs (fst (fst f_r1)).
Definition f_kn1 : list kentry := Eval vm_compute in kn_after f_r1 kn_F2.
(* [comment removed for export] *)
Definition f_sr2i : list expr := Eval vm_compute in sr_after_call_j f_sr1 KEPT_AL 39.
Definition f_kn2i : list kentry := Eval vm_compute in kn_acall f_kn1.
Definition f_r2 := Eval vm_compute in runH scr0 (SS 0x6333c f_sr2i [] f_kn2i 71).
Definition f_sr2 : list expr := Eval vm_compute in s_regs (fst (fst f_r2)).
Definition f_kn2 : list kentry := Eval vm_compute in kn_after f_r2 f_kn2i.

Definition paylen_x : expr := Eval vm_compute in nth 13 h_srK (ELit 0).    (* [comment removed for export] *)
Definition pay_x : expr := Eval vm_compute in nth 12 h_srK (ELit 0).       (* [comment removed for export] *)
Definition b1s_x : expr := EExt true 0 1 (EVar 42).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JR (i : nat) : expr := EVar (13 + i).
Definition sr_R : list expr :=
  [ELit 0; ELit 0x632b4; spx (-128); ELit 0x10800; ELit 0x1381d0; JR 5; JR 6; JR 7;
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
ltac2:(KReplay.run1 (kr_t_V23Hdr_defs ()) [] "h02b0h12b1p;2p;1p;3g0000j2@Tg000Jj1;Tg000hj24Tg001Nj2?Tg002Gj2<Tg0031j15Tg003Oj2:Tg003lj29Tg004Ij13Tg004nj27Tg005Nj28Tg005kj1>Tg006dj36Tg007@j3=Tg007Zj10Tf0R0#3#3p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g0089R1g008YR2'@g0099R3g009W#2#2#2R4#;R51450f1R6,45'?'<%24R4#5/:6,90%34#2#2#2#5'7'8X03g00:<#1#1#1#1#1#1#1#1#>R4563X13;64==12do"). Qed.   (* [comment removed for export] *)

Section VP1.
Lemma h_itinS :
  (s_pc (fst (fst h_rS)), snd (fst h_rS)) = (0x1139cc%Z, [SCBr true BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 41 h_srS h_knS = Some h_scS
  /\ (sc_ret h_scS, sc_f h_scS, sc_fd h_scS, sc_s h_scS, sc_l h_scS) = (0x114480%Z, 0x127cc0%Z, 2%Z, ELit 0x1d52e, ELit 31)
  /\ (s_pc (fst (fst h_rS2)), snd (fst h_rS2), log_win_b 0 (s_log (fst (fst h_rS2)))) = (0x63334%Z, [], true)
  /\ (sr_mismatch f_rvlS idb h_srS2 sr_F2 0, kn_missing h_knS2 (map (kmap f_rvlS idb) kn_F2)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Hdr_defs ()) ["VP1"] "p&0p;1p;2p;4p;3p;<p;5g00:[j1hTg00;;j2NTg004Ij10Tg00;[j11Tg007Zj12Tg00<@j1?Tg00=Ik40<Tg00>Vj1`Tg00?6j39Tg00?Vj4XTg007@j3ETg00@6k103Tg0031j16Tg00@Xj1ATg00Aaj3bTg00Bjj2oTg00D5j3fTg00E@j2eTg00FKj2TTg00GUk407Tg00H`j2MTg00Ikk302Tg00K6l<xTg00L?j2lTg00Laj2QTg0000j2[Tg00M<j4^Tg00MWj3aTg00N4j1kTg00O;j3nTg00OXj5wTg00P`j1vTg00Qdj1|Tg00Rfj1}Tg00Sij1uTg00Tkk100Tg00Umk101Tg00W5j2tTg00X<j5sTg00YIk204Tg00ZOj4rTg00Zkk205Tg00\7j1cTg00\Uj3dTf0R0#0#0#0p=S%10#0#0#1p=7%10#1#0#0p=8%10#1#1#0p=J%00#1#1#0p=_%00#6p=m%60#Ap=B%20#2p=i%00#0#1#0#0#1#1#1#1p=L%10#0#0#0p=4%00#0#0#6p=5%00#0#1#0p=;%00#0#0#0#0#0#0#6p=I%00#1#0#1p=\%10#0#1#1#0#0#0#0p=K%10#1#0#1p=W%00#cp=j%20#2#2#2p=D%00#0#0#0#0#0#0#0p=P%00#1#1#1p=@%00#0#0#0p=3%00#0#1#1p=>%10#0#1#0p=Og00]`R1f2R2#?f1R3#?=91039p=GA91309912p=U%?3=910p=q%10#1#1#1p=F%10#1p=p%10#1#1#1#1#1#1#1p=Z%00#0#0#1p=Y%00#0p=g%c0,T3p>0;f3R4/T2?d30p>0:%10#0p>09%00#1#0#0p==%00#1#0#1#1p>08%00#0#1#0#0p>06%00#0#1p=H%00#1#0p=]%63/M0p=~g00^iR5A9530792p=R%02#6/M3=950p=<f4R6/T4?d23=950p=C1M23=950p={%03#6,M2=950p=z1M641M23=950595p=y%c4,T6?d23=950p=:f6f5P6P4P2P3CXP0CXp=Vg0099R0g00`4R3#hR2'NR4P0P2g009WR6#S#7#8#J#_#mg008YR7g00aA%06R8#1R9#Bg00:<R:#iR;#2R<#2R=#2R>#2R?#2R@#?RAH0<%`3RB593CXR3;E3g00b3RC$03RD%L6#7#4#5RE%68RF%06#;#4#7#IRG%\6#4#4#K#BRHPHPHg00c<RI#ARJ%W6#\#;#J#BRK%16RL#1RM#1RN#1RO#BRPg00cZRQ%?:RR%0LRL#0RS#SRT#j#A3bRU%2@R@#2#D#D#D#D#DRV#2RW#2RX#2RY#2RZ#2R[#2R\#2R]#2#DR^%AG%08R8#0R_#0R`#4#P#B%06#@#3#>#O#5Ra#A%2^#DRb%2bRb%2bRb%66Rc#A%DbRb#?%2bRb%2bRb%2bRb%2bRb%2bRb%2bRb%AE%?VRV%?WRW%2b#i#D#DRb%2bRb%2bRb%2b%`13G3G9G\]9GZ[9GXY3U5UP3G3G3G5UP7UP'q3G3U7UU'qPJ%L6#7#8#5RUP@PHPJ%L6#7#W#5P@PHPJ%L6#7#F#5RYP@PHPJ%L6#7#O#5P@PJPJ%L6#7#7#5RHP@PJPJ%L6#O#7#5RXP=%1O#p#ZRO#p#FR[#1RZ#1#Z#Z#Z#Z#Z#BPR%19R]#4P@PWPR%S]R]#0P@PVPR%09R9#4P@PAPR%S9R9#0P@%?;PR%18R8#4P@%??R?PR%S8R8#0P@%AFRAPR%4_P@%16#Y#7#7#O#mRV#A%6`RW,oR%PO#P#P#I%0`R`#0RO#g#3R\#3Rb#S#3Rd#0#P#P#I5fR20;RdRe%6dRd'ePR%gN#jP@PJH0:PR%SMRM#0P@PJPR%4LP@PJPRPTP@PJPRP]P@%B`9bQRPRP9P@&096#>#Y#=#3#BPRP8P@PAPRPOP@%B_R_9bQRPRPMP@%36#W#F#;#3#B&086#;#3#IRM%0Z#F#J#P#I5f?1o?W1T?IR?%6bRb'ePePdP?PbH07&066#J#3#I,TJ%1S#g#3#I'e1MbH%H6#>#J#_#8%H6#>#J#@#4%H6#>#J#4#3%H6#>#J#O#_%L6#W#4#5%;6#@#J#8#Y#6%;6#@#F#3#7#6%>6#@#F#3#7#6%06#@#3#;#I%H6#8#3#F#=%06#K#>#F#5PJ%06#@#3#;#Y#5RbP@%AbPJ%06#@#3#;#\#5P=%?>R>%H6#8#3#7#O%06#@#3#>#I%H6#8#3#8#=%06#@#3#>#=#5%H6#8#3#W#=%06#@#3#>#4#5%H6#8#3#F#3%]6#8#Y#3#4%06#K#4#4#5R=1TJ=@02_;%\6#4#=#=#4%06#K#4#O#5'~%\6#4#=#_#Y#6%06#K#4#W#5R_PJP_P@%?<%]6#8#;#>#4%06#K#4#F#5%]6#8#;#=#=%06#K#7#;#5R<PJP<P@%6\R\#A%]6#8#;#=#8%06#K#7#7#5%]6#8#=#=#4%6[9f>c1MI\%`5R\3R7<M3<DC3<3<DC3{3R3<5za3<3<3<DCDC3<Dy3<7<X7<Y7<U3R3R3RD:D:D:D:D:D:D:D:3R3RD:D:D:D:D:D:D:DCDCDCDCDCDCM<x,lCRU;EURY1N00RX/N0Ra/N1RM/N1RIPMP1PaP1PXP0P0P0PGPEPFFVPKPPFVRP;EPRKg0089RF,N4REP4PFP0P2PVPBP7FVR7;E7RBg00dFRV#hRG%h5R>'NRcPGP>%`V99V:P\CXR\;E\RV'QR['QR6'Q1[43PYP61[DUPKP[1[IPPBPV1[E71[c\C^C^C^C^P0P2g00deRV1NV2RBg00f3R[g00g?3aRK7a2#kAnV2KCX=E43g00h8g00i3P^g00j0g00jjDwg00kdR^,lC5EDPMP1PaP1PXP0P0P0%v^%|^%}^FV%u^&00^FV=EIPP4PFP0P2g00l^9aB[R[9aV2RB#kAnV2[&01B,t:FV=EE7PGP>g00mXR>g00nSRGg00oPg010KP:Dsg011EP5P5204>Gg012@Cr+05CX=Ec\'Q'Q'Q'Qdo"). Qed.

Lemma h_itinO :
  (s_pc (fst (fst h_rO)), snd (fst h_rO)) = (0x1139cc%Z, [SCBr true BC_LTU (EVar 7) (EAlu ALU_ADD cfglen_x (ELit 6)); SCBr false BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 44 h_srO h_knO = Some h_scO
  /\ (sc_ret h_scO, sc_f h_scO, sc_fd h_scO, sc_s h_scO, sc_l h_scO) = (0x114480%Z, 0x127cc0%Z, 2%Z, ELit 0x14389, ELit 31)
  /\ (s_pc (fst (fst h_rO2)), snd (fst h_rO2), log_win_b 0 (s_log (fst (fst h_rO2)))) = (0x63334%Z, [], true)
  /\ (sr_mismatch f_rvlO idb h_srO2 sr_F2 0, kn_missing h_knO2 (map (kmap f_rvlO idb) kn_F2)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Hdr_defs ()) ["VP1"] "p&0p;1p;2p;4p;3p;<p;5g00:[j1hTg00;;j2PTg007Zj12Tg00<@j1>Tg004Ij10Tg013:j4nTg014Ck30<Tg00;[j11Tg00Aaj3TTg00=Ij4fTg00>Vj1bTg00?6j35Tg00?Vj4STg007@j3DTg00@6j1zTg0031j18Tg00@Xj1@Tg00FKj2VTg00D5j3ZTg00Bjj2oTg00E@j2iTg00GUk40:Tg00H`j2OTg00Ikk306Tg00K6l<{Tg00L?j2jTg00Laj2UTg0000j2]Tg00M<j4aTg00MWj3eTg00N4j1kTg00O;j3lTg00OXj5yTg00P`k100Tg00Qdj1xTg00Rfk101Tg00Sik102Tg00Tkj1wTg00Umj1vTg00W5k204Tg00X<j5uTg00YIk207Tg00ZOk408Tg00Zkj2tTg00\7j1gTg00\Uj3dTf0R0#0#0#0p=Q%10#0#0#1p=7%10#1#0#0p=9%10#1#1#0p=K%00#1#1#0p=c%00#8p=m%00#0p=`%00#0#0#0p=3%00#0#0#0#0#0#0#0p=H%80#@p=<%20#2#2#2p=F%20#2p=p%00#0#1#0#0#1#1#1#1p=M%10#0#0#0p=4%00#0#0#8p=6%00#0#1#0p=A%00#0#0#0#0#0#0#8p=L%00#1p=R%10#0#1#1#0#0#0#0p=J%00#1#0#0p=;%00#0#1#1p==%00#gp=s%00#1#1#1p=C%10#0#1#0p=Wg00]`R1f2R2#>f1R3#>=51035p=IA51309512p=\%>3=510p=r%10#1#0#1p=_%10#1#1#1p=G%10#1p=q%10#1#1#1#1#1#1#1p=[%00#0#0#1p=Y%g0,V3p>0>%10#0p>0=%00#1#0#1#1p>0;%00#0#1#0#0p>09%00#0#1p=E%00#1#0p=^%83/O0p>05g00^iR4A5430752p=N%02#8/O3=540p=?f4R5f3R6'V?d23=540p=B1O23=540p>03%03#8,O2=540p=~1O561O23=540554p=}%g6,V5?d23=540p=:f6R7f5R8;d5Ad623=540554p=|P7P8P5P6P2P3CSP0CSp=Xg0099R0g00`4R3#hR2'PR6P0P2g009WR5#Q#7#9#K#c#mR8g008YR7g015LR9g00:<R:#2R;#2R<#2R=#2R>#2R?#2R@#2RA#>RBg00cZRCg016>g016jg017V%05RD#0RE#0RF#0RG#0RH#0RI#`#3RJ#3RK#Q#3RL#H#H#HRM#`#H#<P7P:P;%2ARA#2#F#F#F#F#FRN#pRO#2RP#2RQ#2RR#2RS#2RT#2#FRU#2RV#>RWCnRX40<%15RY#0RZ#0R[#0R\#1#<3Tg018BR]P:P;%>URUCn3TR^%<ZR_3TCfP]g00aA%1DR]#<PBCf%b3R`553Ra553CSRb;Dbg00b3Rc#zRd%M5#7#4#6Re%8DRD%05#A#4#7#LRf%R5#R#4#4#J#<RgPgPgg00c<Rh#@Ri%;5#=#4#7#<Rj%1YRY#1Rk#1Rl#<Rm%>:Rn%`\R\#s#@5TCRo%2VRV#2Rp%@f%4G#H#<%05#C#3#=#W#6Rq#@%2p#FRr%2rRr%2rRr%85Rs#@%FrRr#>%2rRr%2rRr%2rRr%2rRr%2rRr%2rRr%@e%>NRN%2r#p#F#FRr%2rRr%2rRr%2r%b13I3I9IST9IQR9IOP7\X5\m3I3I3I5\m7\m'r3I3\7\o'rPi%M5#7#9#6RoPAPgPi%M5#7#_#6PAPgPi%M5#7#G#6RPPAPgPi%M5#7#W#6PAPiPi%M5#7#7#6RgPAPiPi%M5#W#7#6ROP>%1l#qRl#[RR#q#GRQ#1RT#1#[#[#[#[#[#<Pn%1]RS#4PAPXPn%QSRS#0PAPNPn%0]R]#4PAPBPn%Q]R]#0PAP^Pn%1ERE#4PA%>@R@Pn%QERE#0PA%@DR^Pn%4FPA%15#Y#7#7#W#mRN#@1V@hRXP;PU1V@sP;PWP@PDP;%>VRV%8lRl9ZUhAZWhlAZVhl%8GRG,on%HR#H#H#L%8M5Zn20>nLRM%8LRL'iPn%QkPAPiPn%QYRY#0PAPiPn%4ZPAPiPnP\PAPiPnPSPA%<H9TCnPnP]PA&0=5#=#Y#;#3#<PnPEPAP^PnPIPA%<FRF9TCnPnPYPA%35#_#G#A#3#<&0;5#A#3#LRY%0T#G#K#H#L5Z@1o@G%8KRK,iXPMPLPXPKH0:&095#K#3#L,Vi%1[#`#3#L'i1OKg%E5#=#K#c#9%E5#=#K#C#4%E5#=#K#4#3%E5#=#K#W#c%M5#_#4#6%A5#C#K#9#Y#8%A5#C#G#3#7#8%=5#C#G#3#7#8%05#C#3#A#L%E5#9#3#G#;%05#J#=#G#6Pi%05#C#3#A#Y#6RKPA%@KPi%E5#9#3#7#R#6P>%>?R?%E5#9#3#7#W%05#C#3#=#L%E5#9#3#9#;%05#C#3#=#;#6%E5#9#3#_#;%05#C#3#=#4#6%E5#9#3#G#3%^5#9#Y#3#4%05#J#4#4#6R>1Vi>@06F<%R5#R#4#;#;#4%05#J#4#W#6+05%R5#R#4#;#c#Y#8%05#J#4#_#6RFPiPFPA%>=%^5#9#A#=#4%05#J#4#G#6%^5#9#A#;#;%05#J#7#A#6R=PiP=PA%8JRJ#@%^5#9#A#;#9%05#J#7#7#6%^5#9#;#;#4%8Q9Z?s1OhJ%b4RJ3N7?Y3?DB3?3?DB4033N3?5~q3?3?3?DBDB3?D}3?7?O7?P7?o3N3N3ND:D:D:D:D:D:D:D:D:3N3N3NDBF|D:D:D:D:D:D:D:DBDBDBDBDBDBM<{,jcRo;DoRP1P00RO/P0Rq/P1RY/P1RhPYP1PqP1POP0P0P0PfPePDFXPjPmFXRm;DmRjg0089RD,P6ReP6PDP0P2PNP`P7FXR`;D`RNg00dFRf#hR?%h4Rs'PRQP?Ps%bf95f:PJCSRJ;DJRf'UR5'URA'U1]6bPPPA1]doPjP51]hmPNPf1]e`1]QJCaCaCaCaP0P2g00deRf1Pf2RNg00f3R5g018b3eRj7e2#kAlf2jCSP0P2P8P7P9PBg019[=TC_Cf=53aCS5D6g00h8g00i3Ppg01:Xg01;RDyg01<LRp,jc5DdPYP1PqP1POP0P0P0&00p%xp&01pFX&02p%wpFX=DhmP6PDP0P2g01=F9eN5R59ef2RN#kAlf25%vN-04:FX=De`P?Psg01>@Rsg00nSR?g01?;g010KP:Dug01@6P4P4207s?g012@H08'tCS=DQJ'U'U'U'Udo"). Qed.

Lemma f_itin :
  (s_pc (fst (fst f_r1)), snd (fst f_r1), s_log (fst (fst f_r1))) = (0x10e818%Z, [], [])
  /\ (nth 1 f_sr1 (ELit 0), nth 10 f_sr1 (ELit 0), nth 2 f_sr1 (ELit 0), nth 4 f_sr1 (ELit 0))
     = (ELit 0x6333c, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ kn_vars_lt 39 f_kn1 = true /\ kn_acall f_kn1 = f_kn2i
  /\ (s_pc (fst (fst f_r2)), snd (fst f_r2), s_log (fst (fst f_r2))) = (0x10e4e0%Z, [], [])
  /\ (nth 10 f_sr2 (ELit 0), nth 2 f_sr2 (ELit 0), nth 4 f_sr2 (ELit 0)) = (ELit 2, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x1381d0).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3g00:[j1fTg00;;j2WTg004Ij10Tg00>Vj1eTg00?Vj4?Tg007@j3<Tg007Zj19Tg00<@j1aTg00\7j1\Tg00@Xj1NTg00Aaj3_Tg00;[j11Tg0031j17Tg00Bjj2gTg00D5j3bTg00E@j2pTg00FKj2OTg00GUj4{Tg00Ikj3xTg00H`j2LTg00Laj2DTg0000j2TTg00M<j4ZTg00MWj3^Tg00N4j1mTg00O;j3lTg00Umj1kTg01A1j2tTg01B8j1sTg00\Uj3dTg00?6j3BTg01C5j4iTf0R0#0#0#0#1p=J%10#1#0#1p=X%00#0#0#0p=2%00#0#1#1p=8%00#0#0#7p=3%10#0p=h%10#1#0#0p=5%70#Np=Ig00]`R1P1f1R2P0C?p=`f2R3P1P2P0C?p=S%00#1#1#1p=>%10#0#1#0p=P%00#0#1#0#0#1#1#1#1p=F%10#0#0#1p=6%90#9p=j%00#1p=K%10#0#0#0p=4%10#0#1#1#0#0#0#0p=E%10#1#1#1p==%10#1#1#1#1#1#1#1p=R%10#1p=r%00#0#0#0#0#0#0#0p=Q%00#0#0#0#0#0#0#7p=H%00#0p=Y%\0,O2p=qf3R4/O3?d20p=}%00#1#0#0p=:%00#0#1#0p=A%00#1#0#1#1p=|%10#1#1#0p=U%00#0#1#0#0p=z%10#0#1#1p=y%00#0#1p=C%00#1#1#0p=o%00#1#0p=[%72/L0p=wg00^iR5AB5207B3p=V%03#7/L2=B50p=;f4R6/O4?d32=B50p=@1L32=B50p=v%02#7,L3=B50p=u1L641L32=B505B5p=n%\4,O6?d32=B50p=GP1P2g01CQP0Cip=]%90#9#9#9p=MP1P2g01DKP0Cip=cg0099R0g00`4R2#fR3'WR6g01EER4#fR7'WR8P6P7P0P3g009WR9#0#J#X#2#8#3%e2R2C?%e4R4C?R:;<:1W11R;/W1R</W1R1%h9#8#8#8#5#Ig00:<R=#9R>#9R?#9R@#9RA#9RB#9RC#aRD'`g00cZRE%a=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#\#N3_5S;%09#>#2#8#P#3RM#NRN5S<RO;<ORPg0089RQg008YRR;<RRS%f5RTg00c<RU#NRV%F9#6#5#3RW%jCRC%K9#K#4#4#E#IRXPV%F9#6#X#3PCPXPV%F9#6#=#3RYPCPXPV%F9#6#P#3PCPVPV%F9#6#6#3RXPCPVPV%F9#P#6#3RZPA%19R[#1R\#1R]#=#RR^#r#=R_#1R`#1#R#R#R#R#R#I%7IRI,g=%Q^#Q#Q#H%0L#2RL#2R^#0#Y#2Ra#0#Q#Q#H5b=1q=aRb%7aRa'pP=%0]#Y#\PCPVC}P=%0\#YR\#0PCPVP=%0[R[#4PCPVP=%0[R[#YR]#0PCPVP=%1FRc#4PC%IJ9_E=P=%2cPC%h9#8#J#:#2#IP=%4GPC%IFRFP=PKPC%IHRH9_E=P=P\PC%29#X#=#A#2#I%|9#A#2#HR\%0`#=#U#Q#H5bD1gDIPbPa1ODU%7^R^C{%z9#U#2#H,OV%1[#Y#2#H'pP^PX%F9#6#y#3PW%C9#8#U#>#4%C9#8#U#4#2%C9#8#U#P#o%F9#X#4#3%A9#>#U#5#J#7%A9#>#=#2#6#7%89#>#=#2#6#7%09#>#2#A#H%C9#5#2#=#:%09#E#8#=#3PV%09#>#2#A#J#3RWPC%NWPV%C9#5#2#6#K#3PA%aBRB%C9#5#2#6#P%09#>#2#8#H%C9#5#2#5#:%09#>#2#8#:#3%C9#5#2#X#:%09#>#2#8#4#3%C9#5#2#=#2%[9#5#J#2#4%09#E#4#4#3RW1OVW?xH?%K9#K#4#:#:#4%09#E#4#P#3'w%K9#K#4#:#o#J#7%09#E#4#X#3RHPVPHPC%a@%[9#5#A#8#4%09#E#4#=#3%[9#5#A#:#:%09#E#6#A#3R@PVP@PC%7LRL#N%[9#5#A#:#5%09#E#6#6#3%[9#5#:#:#4%79%7_5bB1LUL%e53V7;\3;D@3;3;D@3v3V3;5uM3;3;3;D@D@3;Dn3;7;Z7;YDn3V3VDGDGDGDGDGDGDGDG3V3VD@D@D@D@D@D@RY;<YRZP6P7P0P3%09#J#5#6#5#3P2C?P4C?R4=<84R2%\]#N9_E=,`F=S;NRN=<<NRF'DR='DRE'DR]'D1T8:PPP]1T1OPSPE1TQRPZP=1TTYP2PF1T841T<NCZCZCZCZCZP6P7P0P3g00deRF1WF3R2g00f3RYg01FP3^R=7^3RZ#mAlF3=C?%kZC?=<8:1]>V%jCRC/]V'`1]?V5S;1]AV5S<=<1O%9C#M#M#M#M#M#M#Mg01GIRO't=<QR%sOg01HC5<TP6P7P0P3g01I>9^2YRY9^F3R2#mAlF3YC?%k2C?=<841cCV1c?V'`1cAV5S;=<<N'D'D'D'D'Ddo"). Qed.

Lemma h_itinK :
  (s_pc (fst (fst h_rK)), s_log (fst (fst h_rK)), s_next (fst (fst h_rK))) = (0x63410%Z, [], 48%nat)
  /\ paylen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 7) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6))
  /\ pay_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 6) cfglen_x) (ELit 6)
  /\ (sr_mismatch r_rvl idb h_srK sr_R 0, kn_missing h_knK (map (kmap r_rvl idb) kn_R)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g00:[j1:Tg00;;j2>Tg00;[j14Tg004Ij10Tg0031j1;Tg00>Vj1BTg00?Vj47Tg007Zj12Tg007@j33Tg00<@j1?Tg00\7j1GTg00@Xj19Tg013:j4ETg014Cj3ATg00Aaj3=Tg00Laj28Tg0000j2<Tg00M<j4@Tg00MWj3DTg00N4j1OTg00Umj1NTg01J7j1MTg00X<j5LTg00YIj2KTg00ZOj4JTg00Zkj2ITf0R0#0#0p=H%00#0#0#0p=F%20#2#2#2p=1%20#2p=C%00#0#0#0#0#0#0#0p=6g00cZR1f1;=0p=5g0099R0g01EER2#:R3'>R4g00dFR5'>R6P4P5P0P3g009WR7#4#0#H#4#4#0#4#0#F#4#F#;%B2C7g00:<R2#2R8#2#1R9#2R:#C#1#1#1#1#1#1#1#1R;#2R<#C#1C7R=;3=g00]`R>%?:R:g017VR?%G7#9R@g016>g016j%07#6#6#6#6#6#6#6#;#9g008YP2P8%?<CE5A?%47#0R7#H#4#;#93=g018BP2P8%?;CE3=R;3A'5%G7#9R8'5R<;3<RA%?9R9/5;%;7#9R7'5R;=3>;RB%:5RCg00^iRD#:RE'>RFPCPE%B5%BDC7RG;3GRH'8RI'81<6=PAPI1<><PBPH1<>;1<FGC@C@C@P4P5P0P3g00deR3g00`4#:R01>30g00f3g01K@3D3DR0#O%N0C7%M0C7=36=g01L9g019[R=9A?@,5:/5853>g01M6A=19=/5753>PCPEg01N0REg00nSRCg01Njg01OdP2DLg01P]PDPD1KECg01QWCJ'IC7=3FG'8'8'8do"). Qed.
End VP1.
