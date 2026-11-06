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
Proof.
ltac2:(KReplay.run1 (kr_t_O23Hdr_defs ()) ["VP1"] "p&0p;1p;2p;4p;3p;<p;5g00:[j1dTg00;;j2PTg004Ij10Tg00;[j11Tg007Zj12Tg00<@j1CTg00=Ik407Tg00>Vj1^Tg00?6j3;Tg00?Vj4XTg007@j3JTg00@6j1zTg0031j1:Tg00@Xj1DTg00Aaj3`Tg00Bjj2mTg00D5j3eTg00E@j2cTg00FKj2TTg00GUk404Tg00H`j2OTg00Ikk303Tg00K6l<vTg00L?j2kTg00Laj2QTg0000j2YTg00M<j4\Tg00MWj3[Tg00N4j1iTg00O;j3jTg00OXj5uTg00P`j1tTg00Qdj1sTg00Rfj1rTg00Sij1qTg00Tkj1{Tg00Umj1pTg00W5j2|Tg00X<j5}Tg00YIj2~Tg00ZOk400Tg00Zkk201Tg00\7j1bTg00\Uj3aTf0R0#1#1p=H%10#1#1#1p=<%10#0#1#0p=A%10#0#0#1p=7%00#1p=R%00#0#0#:p=3%:0#Dp=G%20#2p=g%00#0#1#0p=9%00#1#1#1p=4%00#0#0#0p=8%00#0#0#1p=5%10#1#1#1#1#1#1#1p=N%10#1#1#0p==%00#:p=o%00#1#0#0p=6%00#0#0#0#0#0#0#0p=E%00#bp=h%20#2#2#2p=I%10#0#0#0p=?g00]`R1f2R2#Cf1R3#C=;103;p=LA;1309;12p=U%C3=;10p=f%00#0#0p=F%10#1#0#0p=@%00#1#1#0p=n%00#0#1#1p=_%00#0p=Z%b0,T3p>06f3R4/T2?a30p>05%00#1#0#0#0p=M%10#0p=l%00#0#1p=W%:3/O0p>02%00#1#0p=]g00^iR5A;5307;2p=S%02#:/O3=;50p=Bf4R6/T4?a23=;50p=K1O23=;50p=y%03#:,O2=;50p=x1O641O23=;505;5p=w%b4,T6?a23=;50p=>f6f5P6P4P2P3CXP0CXp=Vg0099R0g00`4R3#dR2'PR4P0P2g009WR6#H#<#A#7#R#3g008YR7g00aA%06R8#1R9#Gg00:<R:#gR;#2R<#2R=#2R>#2R?#2R@#CRAH07%^3RB5;3CXR3;J3g00b3RC#zRD%06#9#4#8#5#3RE%:8RF%H6#N#=#=#oRG%66#6#6#E#GRHPHPHg00c<RI#DRJ%H6#R#6#7#<#GRK%16RL#1RM#1RN#1RO#GRPg00cZRQ%C:RR%0LRL#8RS#h#D3`RT%2@R@#2#I#I#I#I#IRU#2RV#2RW#2RX#2RY#2RZ#2R[#2R\#2#IR]%DG%08R8#0R^#0R_#?#E#G%06#6#4#A#6#3R`#D%2]#IRa%2aRa%2aRa%:6Rb#D%IaRa#C%2aRa%2aRa%2aRa%2aRa%2aRa%2aRa%DE%CURU%CVRV%2a#g#I#IRa%2aRa%2aRa%2a%^13L3L9L[\9LYZ9LWX3U5UP3L3L3L5UP7UP'f3L3U7UT'fPJ%F6#7#@#5#R#3RTP@PHPJ%06#9#4#8#n#3P@PHPJ%06#9#4#8#?#3RXP@PHPJ%06#9#4#8#_#3P@PJPJ%06#9#4#8#9#3RHP@PJPJ%06#9#4#5#9#3RWP=%1O#H#NRO#H#<RZ#1RY#1#N#N#N#N#N#GPR%19R\#?P@PVPR%F\R\#0P@PUPR%09R9#?P@PAPR%F9R9#0P@%C;PR%18R8#?P@%C?R?PR%F8R8#0P@%DFRAPR%1^#ZRU#0P@%16#5#R#A#9#3RV#D%:_R[,mR%8O#E#E#E#3%0_R_#0RO#Z#8Ra#8Rc#F#8Rd#0#8#E#E#35eR206RdRe%:dRd'cPR%ZN#hP@PJH05PR%FMRM#0P@PJPR%?LP@PJPRPSP@PJPRP\P@%G_9`QRPRP9P@%?6#A#H#5#@#GPRP8P@PAPRPOP@%G^R^9`QRPRPMP@%16#H#7#A#4#@#G%M6#A#E#3RM%0Y#<#=#8#E#35e?1m?[1T?IR?%:cRc'cPePdP?PcH04%1U#l#E#3,TJ%l6#6#E#3'c1OcH%F6#7#@#5#8%F6#7#@#5#@%F6#7#@#9#6%F6#7#@#6#A%06#9#4#6#9#3%56#_#A#5#5#:%Z6#6#=#7#R#7#:%Z6#?#=#7#R#7#:%06#6#4#?#A#3%W6#5#=#7#@%M6#4#A#7#3PJ%W6#5#=#9#H#3RcP@%DcPJ%06#6#4#?#<#3P=%C>R>%W6#5#=#6#9%06#6#4#7#A#3%W6#5#=#n#@%06#6#4#7#=#3%W6#5#=#4#@%06#6#4#A#9#3%W6#5#=#7#?%M6#4#A#H#8%M6#4#<#9#3R=1TJ=@03^;%66#_#<#7#?%M6#4#<#6#3+02%R6#8#<#=#H#5#:%M6#4#<#4#3R^PJP^P@%C<%]6#5#<#=#8%M6#4#<#7#3%]6#5#<#=#@%M6#4#<#@#3R<PJP<P@%:aRa#D%]6#5#N#6%M6#?#8#_#3%]6#9#5#<#8%:Z9e>b1OIa%^5Ra3S7BM3BDK3B3BDK3y3S3B5x`3B3B3BDKDK3BDw3B7BW7BX7BT3S3S3SD>D>D>D>D>D>D>D>3S3SD>D>D>D>D>D>D>DKDKDKDKDKDKM<v,kCRT;JTRX1P00RW/P0R`/P1RM/P1RIPMP1P`P1PWP0P0P0PGPEPFFVPKPPFVRP;JPRKg0089RF,P4REP4PFP0P2PVPBP7FVR7;J7RBg00dFRV#dRG%d5R>'PRbPGP>%^V9;V:PaCXRa;JaRV'QRZ'QR6'Q1Y43PXP61YDTPKPZ1YIPPBPV1YE71YbaC\C\C\C\P0P2g00deRV1PV2RBg00f3RZg00g?3[RK7[2#iAjV2KCX=J43g00h8g00i3P]g00j0g00jjDug00kdR],kC5JDPMP1P`P1PWP0P0P0%t]%s]%r]FV%q]%{]FV=JIPP4PFP0P2g00l^9[BZRZ9[V2RB#iAjV2Z%pB,|:FV=JE7PGP>g00mXR>g00nSRGg00oPg010KP:D}g011EP5P51~>Gg012@H00+01CX=Jba'Q'Q'Q'Qdo"). Qed.

Lemma h_itinO :
  (s_pc (fst (fst h_rO)), snd (fst h_rO)) = (0xff528%Z, [SCBr true BC_LTU (EVar 7) (EAlu ALU_ADD cfglen_x (ELit 6)); SCBr false BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 44 h_srO h_knO = Some h_scO
  /\ (sc_ret h_scO, sc_f h_scO, sc_fd h_scO, sc_s h_scO, sc_l h_scO) = (0xfffdc%Z, 0x113808%Z, 2%Z, ELit 0x1436d, ELit 31)
  /\ (s_pc (fst (fst h_rO2)), snd (fst h_rO2), log_win_b 0 (s_log (fst (fst h_rO2)))) = (0x62d10%Z, [], true)
  /\ (sr_mismatch f_rvlO idb h_srO2 sr_F2 0, kn_missing h_knO2 (map (kmap f_rvlO idb) kn_F2)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Hdr_defs ()) ["VP1"] "p&0p;1p;2p;4p;3p;<p;5g00:[j1fTg00;;j2NTg007Zj12Tg00<@j1CTg004Ij10Tg013:j4kTg014Ck307Tg00;[j11Tg00Aaj3STg00=Ij4eTg00>Vj1bTg00?6j37Tg00?Vj4TTg007@j3ITg00@6j1uTg0031j18Tg00@Xj1ETg00FKj2VTg00D5j3YTg00Bjj2mTg00E@j2hTg00GUk409Tg00H`j2MTg00Ikk308Tg00K6l<yTg00L?j2jTg00Laj2RTg0000j2\Tg00M<j4`Tg00MWj3aTg00N4j1iTg00O;j3nTg00OXj5xTg00P`j1wTg00Qdj1zTg00Rfj1vTg00Sij1{Tg00Tkj1|Tg00Umj1}Tg00W5j2~Tg00X<k500Tg00YIj2tTg00ZOj4sTg00Zkk203Tg00\7j1dTg00\Uj3cTf0R0#1#1p=W%10#1#1#1p=>%10#0#1#0p=H%10#0#0#1p=9%00#1p=U%00#0#0#8p=3%00#0p=Q%00#0#0#0p=<%00#0#0p=F%00#0#0#0#0#0#0#0p=A%80#Ep=B%20#2#2#2p=J%20#2p=l%00#0#1#0p=:%00#1#1#1p=4%00#0#0#1p=6%10#1#1#1#1#1#1#1p=L%10#1#1#0p==%00#8p=r%00#1#0#0p=5%10#0#1#1p=[%00#dp=q%10#0#0#0p=@g00]`R1f2R2#Cf1R3#C=71037p=KA71309712p=Z%C3=710p=p%10#1#0#0p=D%00#1#1#0p=o%00#0#1#1p=_%d0,V3p>0:%10#0p=g%00#1#0#0#0p=P%00#0#1p=]%00#1#0p=^%83/M0p>06g00^iR4A7430772p=O%02#8/M3=740p=?f4R5f3R6'V?c23=740p=G1M23=740p>05%03#8,M2=740p>041M561M23=740574p>02%d6,V5?c23=740p=;f6R7f5R8;c5Ac623=740574p>01P7P8P5P6P2P3CTP0CTp=Xg0099R0g00`4R3#fR2'NR6P0P2g009WR5#W#>#H#9#U#3R8g008YR7g015LR9g00:<R:#2R;#2R<#2R=#2R>#2R?#2R@#2RA#CRBg00cZRCg016>g016jg017V%05RD#0RE#0RF#0RG#0RH#0RI#Q#<RJ#<RK#F#<RL#A#A#ARM#Q#A#BP7P:P;%2ARA#2#J#J#J#J#JRN#lRO#2RP#2RQ#2RR#2RS#2RT#2#JRU#2RV#CRWCkRX407%15RY#0RZ#QR[#1#B3Sg018BR\P:P;%CURUCk3SR]%BZR^3SCeP\g00aA%1DR\#BPBCe%b3R_573R`573CTRa;Iag00b3Rb#uRc%05#:#4#<#6#3Rd%8DRD%W5#L#=#=#rRe%55#5#5#A#BRfPfPfg00c<Rg#ERh%0\Ri#FRj#W#U#[#U#BRk%1YRY#1Rl#1Rm#BRn%C:Ro%Q[R[#q#E5SCRp%2VRV#2Rq%Ee%@G#A#B%05#5#4#H#5#3Rr#E%2q#JRs%2sRs%2sRs%85Rt#E%JsRs#C%2sRs%2sRs%2sRs%2sRs%2sRs%2sRs%Ed%CNRN%2s#l#J#JRs%2sRs%2sRs%2s%b13K3K9KST9KQR9KOP7ZX5Zn3K3K3K5Zn7Zn'p3K3Z7Zp'pPh%F5#9#D#6#U#3RpPAPfPh%05#:#4#<#o#3PAPfPh%05#:#4#<#@#3RPPAPfPh%05#:#4#<#_#3PAPhPh%05#:#4#<#:#3RfPAPhPh%05#:#4#6#:#3ROP>%1m#WRm#LRR#W#>RQ#1RT#1#L#L#L#L#L#BPo%1\R\#@PAPXPo%F\R\#0PAPNPo%@iPAPBPo%0jPAP]Po%1ERE#@PA%C@R@Po%FERE#0PA%EDR]Po%1F#QRi#0PA%15#6#U#H#:#3RN#E1V@gRXP;PU1V@tP;PWP@PDP;%CVRV%8mRm9YUgAYWgmAYVgm%8GRG,mo%<R#A#A#A#3%8M5Yo20:oLRM%8LRL'hPo%FlPAPhPo%FYRY#0PAPhPo%@ZPAPhPoP[PAPhPoP\PA%BH9SCoPoPjPA%g5#:#[#6#D#BPoPEPAP]PoPIPA%BFRF9SCoPoPYPA%15#W#9#H#4#D#B%P5#H#A#3RY%0T#>#=#<#A#35Y@1m@G%8KRK,hXPMPLPXPKH09%1i#g#A#3,Vh%g5#5#A#3'h1MKf%F5#9#D#6#<%F5#9#D#6#D%F5#9#D#:#5%F5#9#D#5#H%05#:#4#5#:#3%65#_#H#6#6#8%Q5#5#=#9#U#9#8%Q5#@#=#9#U#9#8%05#5#4#@#H#3%]5#6#=#9#D%P5#4#H#9#3Ph%05#5#4#@#[#3RKPA%EKPh%05#5#4#@#>#3P>%C?R?%]5#6#=#5#:%05#5#4#9#H#3%]5#6#=#o#D%05#5#4#9#=#3%]5#6#=#4#D%05#5#4#H#:#3%]5#6#=#9#@%^5#6#=#[#<%P5#4#>#:#3R>1Vh>@08F<%55#_#>#9#@%P5#4#>#5#3+06%55#_#>#[#6#8%P5#4#>#4#3RFPhPFPA%C=%^5#6#>#=#<%P5#4#>#9#3%^5#6#>#=#D%P5#4#>#D#3R=PhP=PA%8JRJ#E%^5#6#L#5%P5#@#<#_#3%^5#:#6#>#<%8Q9Y?t1MgJ%b4RJ3O7?Y3?DG3?3?DG4053O3?604r3?3?3?DGDG3?I023?7?O7?P7?p3O3O3OD;D;D;D;D;D;D;D;D;3O3O3ODGK01D;D;D;D;D;D;D;DGDGDGDGDGDGM<y,jbRp;IpRP1N00RO/N0Rr/N1RY/N1RgPYP1PrP1POP0P0P0PePdPDFXPkPnFXRn;InRkg0089RD,N6RdP6PDP0P2PNP_P7FXR_;I_RNg00dFRe#fR?%f4Rt'NRQP?Pt%be97e:PJCTRJ;IJRe'RR5'RRA'R1\6aPPPA1\cpPkP51\gnPNPe1\d_1\QJC`C`C`C`P0P2g00deRe1Ne2RNg00f3R5g018b3aRk7a2#iAne2kCTP0P2P8P7P9PBg019[=SC^Ce=73`CT5I6g00h8g00i3Pqg01:Xg01;RDxg01<LRq,jb5IcPYP1PrP1POP0P0P0%wq%zq%vqFX%{q%|qFX=IgnP6PDP0P2g01=F9aN5R59ae2RN#iAne25%}N,~:FX=Id_P?Ptg01>@Rtg00nSR?g01?;g010KP:I00g01@6P4P41tt?g012@Cs+03CT=IQJ'R'R'R'Rdo"). Qed.

Lemma f_itin :
  (s_pc (fst (fst f_r1)), snd (fst f_r1), s_log (fst (fst f_r1))) = (0xfa374%Z, [], [])
  /\ (nth 1 f_sr1 (ELit 0), nth 10 f_sr1 (ELit 0), nth 2 f_sr1 (ELit 0), nth 4 f_sr1 (ELit 0))
     = (ELit 0x62d18, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x123d20)
  /\ kn_vars_lt 39 f_kn1 = true /\ kn_acall f_kn1 = f_kn2i
  /\ (s_pc (fst (fst f_r2)), snd (fst f_r2), s_log (fst (fst f_r2))) = (0xfa03c%Z, [], [])
  /\ (nth 10 f_sr2 (ELit 0), nth 2 f_sr2 (ELit 0), nth 4 f_sr2 (ELit 0)) = (ELit 2, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x123d20).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3g00:[j1fTg00;;j2TTg00>Vj1bTg00?Vj4BTg007@j3@Tg007Zj1<Tg00<@j1_Tg004Ij10Tg00\7j1XTg00@Xj1NTg00Aaj3]Tg00;[j11Tg0031j1:Tg00Bjj2gTg00D5j3`Tg00E@j2qTg00FKj2OTg00GUj4yTg00Ikj3xTg00H`j2LTg00Laj2ETg0000j2UTg00M<j4WTg00MWj3\Tg00N4j1lTg00O;j3nTg00Umj1oTg01A1j2tTg01B8j1sTg00\Uj3dTg00?6j3FTg01C5j4jTf0R0#1#1#1#1p=9%00#1p=P%00#0#0#1p=5%10#0#1#1p=S%10#0#1#0p=C%00#:p=k%10#0#0#0p=;%:0#Np=Gg00]`R1P1f1R2P0CBp=^f2R3P1P2P0CBp=Q%00#1#0#0p=4%00#1#1#1p=3%00#0#0#:p=2%00#0#0p=H%10#0#0#1p=7%10#1#0#0p=?%<0#<p=i%00#0#0#0#0#0#0#0p=A%00#0#1#0p=8%00#0#0#0p=6%00#1#1#0p=a%00#0#1#1p=V%10#1#1#1#1#1#1#1p=K%10#1p=h%X0,O2p=rf3R4/O3?d20p=z%10#0p=e%00#1#0#0#0p=J%10#1#1#0p==%00#0p=p%00#0#1p=Z%00#1#0p=Y%:2/L0p=wg00^iR5AF5207F3p=R%03#:/L2=F50p=>f4R6/O4?d32=F50p=D1L32=F50p=v%02#:,L3=F50p=u1L641L32=F505F5p=m%X4,O6?d32=F50p=IP1P2g01CQP0Cjp=[%<0#<#<#<p=MP1P2g01DKP0Cjp=cg0099R0g00`4R2#fR3'TR6g01EER4#fR7'TR8P6P7P0P3g009WR9#9#P#5#S#C#k%b2R2CB%b4R4CBR:;@:1T11R;/T1R</T1R1%;9#S#P#5#;#Gg00:<R=#<R>#<R?#<R@#<RA#<RB#<RC#_RD'^g00cZRE%_=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#X#N3]5Q;%09#4#3#C#4#2RM#NRN5Q<RO;@ORPg0089RQg008YRR;@RRS%f5RTg00c<RU#NRV%H9#7#?#5#P#2RW%iCRC%49#4#4#A#GRXPV%09#8#3#6#a#2PCPXPV%09#8#3#6#;#2RYPCPXPV%09#8#3#6#V#2PCPVPV%09#8#3#6#8#2RXPCPVPV%09#8#3#5#8#2RZPA%19R[#1R\#1R]#9#KR^#h#9R_#1R`#1#K#K#K#K#K#G%:IRI,g=%6^#A#A#A#2%0L#6RL#6R^#H#6Ra#0#6#A#A#25`=1r=aRb%:aRa'qP=%H]#XPCPVCzP=%H\R\#0PCPVP=%0[R[#;PCPVP=%H[R[#0PCPVP=%1FR]#;PC%GJ9]E=P=%6]PC%e9#8#S#5#?#GP=%;GPC%GFRFP=PKPC%GHRK9]E=P=P\PC%19#h#7#C#3#?#G%J9#C#A#2R\%0`#9#=#6#A#25`D1gDIPbPa1ODU%:^R^Cy%eH#a#A#2,OV%e9#4#A#2'qP^PX%09#8#3#6#4#2PW%H9#7#?#5#?%H9#7#?#8#4%H9#7#?#4#C%09#8#3#4#8#2%59#V#C#5#5#:%p9#4#=#7#P#7#:%p9#;#=#7#P#7#:%09#4#3#;#C#2%Z9#5#=#7#?%J9#3#C#7#2PV%09#4#3#;#S#2RWPC%NWPV%09#4#3#;#9#2PA%_BRB%Z9#5#=#4#8%09#4#3#7#C#2%Z9#5#=#a#?%09#4#3#7#=#2%Z9#5#=#3#?%09#4#3#C#8#2%Z9#5#=#7#;%Y9#5#=#S#6%J9#3#9#8#2RW1OVW?xK?%49#V#9#7#;%J9#3#9#4#2'w%49#V#9#S#5#:%J9#3#9#3#2RKPVPKPC%_@%Y9#5#9#=#6%J9#3#9#7#2%Y9#5#9#=#?%J9#3#9#?#2R@PVP@PC%:LRL#N%Y9#5#K#4%J9#;#6#V#2%Y9#8#5#9#6%:9%:_5`B1LUL%b53R7>\3>DD3>3>DD3v3R3>5uM3>3>3>DDDD3>Dm3>7>Z7>YDm3R3RDIDIDIDIDIDIDIDI3R3RDDDDDDDDDDDDRY;@YRZP6P7P0P3%99#P#6#5#=#kP2CBP4CBR4=@84R2%X[#N9]E=,^F=Q;NRN=@<NRF'ER='ERE'ER['E1U8:PPP[1U1OPSPE1UQRPZP=1UTYP2PF1U841U<NCWCWCWCWCWP6P7P0P3g00deRF1TF3R2g00f3RYg01FP3\R=7\3RZ#lAnF3=CB%oZCB=@8:1[>V%iCRC/[V'^1[?V5Q;1[AV5Q<=@1O%<C#M#M#M#M#M#M#Mg01GIRO't=@QR%sOg01HC5@TP6P7P0P3g01I>9\2YRY9\F3R2#lAnF3YCB%o2CB=@841cCV1c?V'^1cAV5Q;=@<N'E'E'E'E'Edo"). Qed.

Lemma h_itinK :
  (s_pc (fst (fst h_rK)), s_log (fst (fst h_rK)), s_next (fst (fst h_rK))) = (0x62dec%Z, [], 48%nat)
  /\ paylen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 7) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6))
  /\ pay_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 6) cfglen_x) (ELit 6)
  /\ (sr_mismatch r_rvl idb h_srK sr_R 0, kn_missing h_knK (map (kmap r_rvl idb) kn_R)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g00:[j1<Tg00;;j2?Tg00;[j11Tg004Ij10Tg0031j1=Tg00>Vj1ATg00?Vj47Tg007Zj12Tg007@j34Tg00<@j1;Tg00\7j1GTg00@Xj19Tg013:j4FTg014Cj3BTg00Aaj3>Tg00Laj28Tg0000j2:Tg00M<j4@Tg00MWj3ETg00N4j1NTg00Umj1MTg01J7j1LTg00X<j5KTg00YIj2HTg00ZOj4ITg00Zkj2JTf0R0#0#0p=C%20#2#2#2p=3%20#2p=D%00#0#0#0#0#0#0#0p=6g00cZR1f1;>0p=5g0099R0g01EER2#<R3'?R4g00dFR5'?R6P4P5P0P3g009WR7#1#0#C#1#0#1#1#0#1#1#1#1#0#1#1#C#=%A2C7g00:<R2#2R8#2#3R9#2R:#D#3#3#3#3#3#3#3#3R;#2R<#D#3C7R=;4=g00]`R>%;:R:g017VR?%G7#9R@g016>g016j%07#6#6#6#6#6#6#6#=#9g008YP2P8%;<CF5B?%17#0R7#C#1#=#93>g018BP2P8%;;CF3>R;3B'5%G7#9R8'5R<;4<RA%;9R9/5;%=7#9R7'5R;=4>;RB%<5RCg00^iRD#<RE'?RFPCPE%A5%ADC7RG;4GRH'8RI'81:6=PAPI1:><PBPH1:>;1:FGC@C@C@P4P5P0P3g00deR3g00`4#<R01?30g00f3g01K@3E3ER0#N%M0C7%L0C7=46=g01L9g019[R=9B?@,5:/5854>g01M6A>19=/5754>PCPEg01N0REg00nSRCg01Njg01OdP2DKg01P]PDPD1HECg01QWCI'JC7=4FG'8'8'8do"). Qed.
End VP1.
