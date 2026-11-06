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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall O2OpenFail_defs O2Open_defs O2Oom_defs O2DirRead_defs O2ReadLoop_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Hdr_defs () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib2O2:O2Hdr_defs4cfgFC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbc59OSSVerify5KrLib2O2:O2Hdr_defs4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs4h_rSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_srSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_knSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_scSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_rS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6f_rvlSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2?O2ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6h_srS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5sr_F2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6h_knS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5kn_F2C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2O2:O2Hdr_defs4h_rOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs8cfglen_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_srOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_knOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_scOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_rO2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6f_rvlOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6h_srO2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6h_knO2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthc59OSSVerify5KrLib2O2:O2Hdr_defs5f_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5f_sr2C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs4f_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5f_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs6f_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs4f_r2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs4h_rKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs8paylen_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5pay_xC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5r_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_srKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs4sr_RC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs5h_knKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2:O2Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPSH : list Z := (0x178e8 :: STOPSL)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH scr ss [].
Definition STOPSH2 : list Z := (0x1780c :: STOPSH)%Z.
Definition runH2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSH2 scr ss [].

(* [comment removed for export] *)
Definition kn_H6 : list kentry :=
  KWord (SA (EVar 6) 0) 1 (EVar 41) :: KWord (SA (EVar 6) 1) 1 (EVar 42) :: KWord (SA (EVar 6) 2) 1 (EVar 43)
  :: KRange (EVar 41) 0 255 :: KRange (EVar 42) 0 255 :: KRange (EVar 43) 0 255 :: kn_ML.

(* [comment removed for export] *)
Definition h_rS := Eval vm_compute in runH (SCR [true] [] []) (SS 0x17714 sr_H [] kn_ML 41).
Definition h_srS : list expr := Eval vm_compute in s_regs (fst (fst h_rS)).
Definition h_knS : list kentry := Eval vm_compute in kn_after h_rS kn_ML.
Definition h_scS : stdio_res := Eval vm_compute in sc_of 41 h_srS h_knS.
(* [comment removed for export] *)
Definition h_srS2i : list expr := Eval vm_compute in sc_sr h_scS.
Definition h_knS2i : list kentry := Eval vm_compute in sc_kn h_scS.
Definition h_rS2 := Eval vm_compute in runH2 scr0 (SS 0x31df4 h_srS2i [] h_knS2i 73).
Definition h_srS2 : list expr := Eval vm_compute in s_regs (fst (fst h_rS2)).
Definition h_knS2 : list kentry := Eval vm_compute in kn_after h_rS2 h_knS2i.

(* [comment removed for export] *)
Definition h_rK := Eval vm_compute in runH (SCR [false; false] [] []) (SS 0x17714 sr_H [] kn_H6 44).
Definition h_srK : list expr := Eval vm_compute in s_regs (fst (fst h_rK)).
Definition h_knK : list kentry := Eval vm_compute in kn_after h_rK kn_H6.

Definition cfglen_x : expr := Eval vm_compute in nth 18 h_srK (ELit 0).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_rO := Eval vm_compute in runH (SCR [false; true] [] []) (SS 0x17714 sr_H [] kn_H6 44).
Definition h_srO : list expr := Eval vm_compute in s_regs (fst (fst h_rO)).
Definition h_knO : list kentry := Eval vm_compute in kn_after h_rO kn_H6.
Definition h_scO : stdio_res := Eval vm_compute in sc_of 44 h_srO h_knO.
Definition h_srO2i : list expr := Eval vm_compute in sc_sr h_scO.
Definition h_knO2i : list kentry := Eval vm_compute in sc_kn h_scO.
Definition h_rO2 := Eval vm_compute in runH2 scr0 (SS 0x31df4 h_srO2i [] h_knO2i 76).
Definition h_srO2 : list expr := Eval vm_compute in s_regs (fst (fst h_rO2)).
Definition h_knO2 : list kentry := Eval vm_compute in kn_after h_rO2 h_knO2i.

(* [comment removed for export] *)
Definition JF (i : nat) : expr := EVar (7 + i).
Definition sr_F2 : list expr :=
  [ELit 0; JF 1; spx (-128); ELit 0x10800; ELit 0x49840; JF 5; JF 6; JF 7;
   ELit 2; EVar 6; JF 10; JF 11; JF 12; JF 13; JF 14; JF 15;
   JF 16; JF 17; JF 18; JF 19; JF 20; JF 21; JF 22; JF 23;
   JF 24; JF 25; JF 26; JF 27; JF 28; JF 29; JF 30; JF 31].
Definition kn_F2 : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) h_knO2.
Definition f_rvlS : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srS2).
Definition f_rvlO : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6] ++ (ELit 0 :: tl h_srO2).
(* [comment removed for export] *)
Definition f_r1 := Eval vm_compute in runH scr0 (SS 0x1780c sr_F2 [] kn_F2 39).
Definition f_sr1 : list expr := Eval vm_compute in s_regs (fst (fst f_r1)).
Definition f_kn1 : list kentry := Eval vm_compute in kn_after f_r1 kn_F2.
(* [comment removed for export] *)
Definition f_sr2i : list expr := Eval vm_compute in sr_after_call_j f_sr1 KEPT_AL 39.
Definition f_kn2i : list kentry := Eval vm_compute in kn_acall f_kn1.
Definition f_r2 := Eval vm_compute in runH scr0 (SS 0x17814 f_sr2i [] f_kn2i 71).
Definition f_sr2 : list expr := Eval vm_compute in s_regs (fst (fst f_r2)).
Definition f_kn2 : list kentry := Eval vm_compute in kn_after f_r2 f_kn2i.

Definition paylen_x : expr := Eval vm_compute in nth 13 h_srK (ELit 0).    (* [comment removed for export] *)
Definition pay_x : expr := Eval vm_compute in nth 12 h_srK (ELit 0).       (* [comment removed for export] *)
Definition b1s_x : expr := EExt true 0 1 (EVar 42).                         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JR (i : nat) : expr := EVar (13 + i).
Definition sr_R : list expr :=
  [ELit 0; ELit 0x1778c; spx (-128); ELit 0x10800; ELit 0x49840; JR 5; JR 6; JR 7;
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
ltac2:(KReplay.run1 (kr_t_O2Hdr_defs ()) [] "h02b0h12b1p;2p;1p;3g0000j2@Tg000Jj1;Tg000hj24Tg001Nj2?Tg002Ej2<Tg002oj15Tg003Mj2:Tg003jj29Tg004Gj13Tg004lj27Tg005Lj28Tg005ij1>Tg006`j36Tg007<j3=Tg007Vj10Tf0R0#3#3p=2%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g0085R1g008UR2'@g0095R3g009S#2#2#2R4#;R51450f1R6,45'?'<%24R4#5/:6,90%34#2#2#2#5'7'8X03g00:8#1#1#1#1#1#1#1#1#>R4563X13;64==12do"). Qed.   (* [comment removed for export] *)

Section VP1.
Lemma h_itinS :
  (s_pc (fst (fst h_rS)), snd (fst h_rS)) = (0x31958%Z, [SCBr true BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 41 h_srS h_knS = Some h_scS
  /\ (sc_ret h_scS, sc_f h_scS, sc_fd h_scS, sc_s h_scS, sc_l h_scS) = (0x31df4%Z, 0x39508%Z, 2%Z, ELit 0x121c9, ELit 31)
  /\ (s_pc (fst (fst h_rS2)), snd (fst h_rS2), log_win_b 0 (s_log (fst (fst h_rS2)))) = (0x1780c%Z, [], true)
  /\ (sr_mismatch f_rvlS idb h_srS2 sr_F2 0, kn_missing h_knS2 (map (kmap f_rvlS idb) kn_F2)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr_defs ()) ["VP1"] "p&0p;1p;2p;4p;3p;<p;5g00:Wj1fTg00;7j2OTg004Gj10Tg00;Wj11Tg007Vj12Tg00<<j1?Tg00=Ek407Tg00>Rj1aTg00?2j39Tg00?Rj4WTg007<j3HTg00@2k103Tg002oj18Tg00@Tj1@Tg00A]j3bTg00Bfj2oTg00D1j3gTg00E<j2eTg00FGj2UTg00GQk404Tg00H\j2MTg00Igk302Tg00K2l<wTg00L;j2lTg00L]j2RTg0000j2\Tg00M8j4^Tg00MSj3_Tg00N0j1kTg00O7j3nTg00OTj5vTg00P\j1uTg00Q`j1tTg00Rbj1sTg00Sej1rTg00Tgj1{Tg00Uij1qTg00W1j2|Tg00X8j5}Tg00YEj2pTg00ZKj4~Tg00Zgk200Tg00\3j1dTg00\Qj3cTf0R0#1#0p=S%00#0#1#1p=;%00#0#1#0p=6%10#0#1#1p=Z%00#0#0#8p=3%80#@p=G%20#2p=j%10#1#0#0p=4%10#0#1#0p=:%10#0#0#0p=7%00#1p=`%10#1#1#0p=K%10#1#1#1p=B%00#8p=m%10#0#0#1p=A%00#0#0#0p=5%00#0p=J%00#dp=i%20#2#2#2p=E%00#0#0#0#0#0#0#0p=D%00#0#1p=Qg00]\R1f2R2#?f1R3#?=91039p=IA91309912p=X%?3=910p=h%10#1p=C%00#1#0#1p=P%00#1#1#0p=V%10#1#1#1#1#1#1#1p=[%d0,U3p>06f3R4/U2?c30p>05%10#1#0#1p=N%10#0#1p=L%00#1#0#0p==%00#1#1#1p=]%83/M0p>01g00^eR5A9530792p=T%02#8/M3=950p=>f4R6/U4?c23=950p=F1M23=950p=z%03#8,M2=950p=y1M641M23=950595p=x%d4,U6?c23=950p=<f6f5P6P4P2P3CWP0CWp=Yg0095R0g00`0R3#fR2'OR4P0P2g009SR6#S#;#6#Z#3g008UR7g00a=%06R8#1R9#Gg00:8R:#jR;#2R<#2R=#2R>#2R?#2R@#?RAH07%a3RB593CWR3;H3g00aoRC$03RD%46#:#7#`#3RE%88RF%76#K#B#:#mRG%S6#A#B#5#7#GRHPHPHg00c8RI#@RJ%08R8#1RK#0#JRL#0RM#1#4#A#GRN%16RO#1RP#1RQ#1RR#GRSg00cVRT%?:RU%0ORO#5RV#i#@3bRW%2@R@#2#E#E#E#E#ERX#2RY#2RZ#2R[#2R\#2R]#2R^#2R_#2#ER`%@G%08R8#0Ra#7#D#G%Q6#;#5#7#3Rb#@%2`#ERc%2cRc%2cRc%86Rd#@%EcRc#?%2cRc%2cRc%2cRc%2cRc%2cRc%2cRc%@E%?XRX%?YRY%2c#j#E#ERc%2cRc%2cRc%2c%a13I3I9I^_9I\]9IZ[3X5XS3I3I3I5XS7XS'h3I3X7XW'hPJ%C6#6#:#P#3RWP@PHPJ%C6#6#:#V#3P@PHPJ%C6#6#:#7#3R[P@PHPJ%C6#6#:#;#3P@PJPJ%C6#6#:#6#3RHP@PJPJ%C6#6#Z#6#3RZP=%1R#C#[RR#C#BR]#1R\#1#[#[#[#[#[#GPU%19R_#7P@PYPU%0_#JR_#0P@PXPU%09R9#7P@PAPU%09#JR9#0P@%?;PU%7KP@%??R?PUPMP@%@FRMPU%78P@%06#C#4#5#V#mRK#@%8aRA,oU%5R#D#D#D#3%0aRa#0RR#J#5RX#5RY#0#J#5R^#0#5#D#D#35gU206U^Rc%8^R^'ePU%JQ#iP@PJH05PU%JPRP#0RQ#0P@PJPU%7OP@PJPUPVP@PJPUP_P@%Ga9bTUPUP9P@%`6#N#7#`#7#GPUPLP@PMPUPRP@%G8R89bTUPUPQP@%06#K#B#N#7#G%L6#V#D#3RQ%0\#B#K#5#D#35g?1o?A1U?IR?%8YRY'ePcP^P?PYH04%SP#D#3,UJ%S6#=#D#3'e1MYH%46#:#A#5%46#:#A#4%46#:#:#=%46#:#4#:%C6#6#N#K#3%16#S#P#Z#4#`#8%16#A#]#;#A#8%J6#A#]#;#A#8%Q6#6#K#K#3%06#=#4#6#4%L6#;#5#N#3PJ%Q6#6#K#B#3RYP@%@YPJ%Q6#6#B#;#3P=%?>R>%06#=#Z#N#6%Q6#6#B#K#3%06#=#Z#B#4%Q6#;#5#6#3%06#=#4#5#4%Q6#;#5#V#3%06#=#4#6#7%16#=#4#=#5%L6#;#P#P#3R=1UJ=@028;%S6#A#:#Z#5%L6#;#P#]#3+01%S6#A#:#4#A#8%L6#;#P#:#3R8PJP8P@%?<%16#=#N#V#4%L6#;#P#4#3%16#=#N#]#7%L6#;#P#B#3R<PJP<P@%8XRX#@%16#=#N#7#5%L6#;#V#V#3%16#=#B#]#=%8]9g>d1MIX%a5RX3T7>Q3>DF3>3>DF3z3T3>5yb3>3>3>DFDF3>Dx3>7>Z7>[7>W3T3T3TD<D<D<D<D<D<D<D<3T3TD<D<D<D<D<D<D<DFDFDFDFDFDFM<w,lCRW;HWR[1O00RZ/O0Rb/O1RQ/O1RIPQP1PbP1PZP0P0P0PGPEPFFYPNPSFYRS;HSRNg0085RF,O4REP4PFP0P2PKPBP7FYR7;H7RBg00dBRK#fRG%f5R>'ORdPGP>%aK99K:PXCWRX;HXRK'RR]'RR6'R1\43P[P61\DWPNP]1\ISPBPK1\E71\dXC^C^C^C^P0P2g00daRK1OK2RBg00eoR]g00g;3_RN7_2#kAnK2NCW=H43g00h2g00hjP`g00idg00j\Dvg00kTR`,lC5HDPQP1PbP1PZP0P0P0%u`%t`%s`FY%r`%{`FY=HISP4PFP0P2g00lL9_B]R]9_K2RB#kAnK2]%qB,|:FY=HE7PGP>g00mDR>g00n=RGg00o8g0101P:D}g010iP5P51p>Gg011bC~+00CW=HdX'R'R'R'Rdo"). Qed.

Lemma h_itinO :
  (s_pc (fst (fst h_rO)), snd (fst h_rO)) = (0x31958%Z, [SCBr true BC_LTU (EVar 7) (EAlu ALU_ADD cfglen_x (ELit 6)); SCBr false BC_GEU (ELit 5) (EVar 7)])
  /\ stdio_call 44 h_srO h_knO = Some h_scO
  /\ (sc_ret h_scO, sc_f h_scO, sc_fd h_scO, sc_s h_scO, sc_l h_scO) = (0x31df4%Z, 0x39508%Z, 2%Z, ELit 0x10bde, ELit 31)
  /\ (s_pc (fst (fst h_rO2)), snd (fst h_rO2), log_win_b 0 (s_log (fst (fst h_rO2)))) = (0x1780c%Z, [], true)
  /\ (sr_mismatch f_rvlO idb h_srO2 sr_F2 0, kn_missing h_knO2 (map (kmap f_rvlO idb) kn_F2)) = ([0%nat], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr_defs ()) ["VP1"] "p&0p;1p;2p;4p;3p;<p;5g00:Wj1gTg00;7j2PTg007Vj12Tg00<<j1@Tg004Gj10Tg012Zj4lTg013ck308Tg00;Wj11Tg00A]j3VTg00=Ej4eTg00>Rj1cTg00?2j34Tg00?Rj4UTg007<j3HTg00@2j1wTg002oj15Tg00@Tj1ETg00FGj2WTg00D1j3[Tg00Bfj2nTg00E<j2hTg00GQk407Tg00H\j2OTg00Igk306Tg00K2l<}Tg00L;j2kTg00L]j2TTg0000j2^Tg00M8j4bTg00MSj3aTg00N0j1jTg00O7j3mTg00OTj5xTg00P\j1vTg00Q`j1yTg00Rbj1zTg00Sej1uTg00Tgj1{Tg00Uij1|Tg00W1j2tTg00X8k500Tg00YEk201Tg00ZKj4sTg00Zgj2rTg00\3j1fTg00\Qj3dTf0R0#1#0p=N%00#0#1#1p=<%00#0#1#0p=7%10#0#1#1p=Z%00#0#0#5p=3%00#0p=B%00#0#0#0p=9%00#0#0#0#0#0#0#0p=A%50#Ep=>%20#2#2#2p=I%20#2p=o%10#1#0#0p=6%10#0#1#0p=:%10#0#0#0p=8%00#1p=`%10#1#1#0p=J%10#1#1#1p=F%00#5p=i%10#0#0#1p=G%10#1p=C%10#1#0#1p=K%00#fp=q%00#0#1p=Sg00]\R1f2R2#@f1R3#@=41034p=LA41309412p=]%@3=410p=p%00#1#0#1p=R%00#1#1#0p=X%10#1#1#1#1#1#1#1p=\%f0,W3p>09%10#0#1p=Q%00#1#0#0p==%00#1#1#1p=_%53/O0p>05g00^eR4A4430742p=M%02#5/O3=440p=?f4R5f3R6'W?d23=440p=D1O23=440p>04%03#5,O2=440p>031O561O23=440544p>02%f6,W5?d23=440p=;f6R7f5R8;d5Ad623=440544p=~P7P8P5P6P2P3CUP0CUp=Yg0095R0g00`0R3#gR2'PR6P0P2g009SR5#N#<#7#Z#3R8g008UR7g014lR9g00:8R:#2R;#2R<#2R=#2R>#2R?#2R@#2RA#@RBg00cVRCg015^g016Jg0176%05RD#0RE#0RF#0RG#0RH#0RI#B#9RJ#9RK#0#B#9RL#A#A#ARM#B#A#>P7P:P;%2ARA#2#I#I#I#I#IRN#oRO#2RP#2RQ#2RR#2RS#2RT#2#IRU#2RV#@RWClRX408%15RY#0RZ#BR[#1#>3Vg017bR\P:P;%@URUCl3VR]%>ZR^3VCeP\g00a=%1DR\#>PBCe%c3R_543R`543CURa;Hag00aoRb#wRc%65#:#8#`#3Rd%5DRD%85#J#F#:#iRe%N5#G#F#9#8#>RfPfPfg00c8Rg#ERh%NGRi#C#K#J#>Rj%1YRY#1Rk#1Rl#>Rm%@:Rn%B[R[#q#E5VCRo%2VRV#2Rp%Ee%Bi#A#>%S5#<#9#8#3Ri#E%2p#IRq%2qRq%2qRq%55Rr#E%IqRq#@%2qRq%2qRq%2qRq%2qRq%2qRq%2qRq%Ed%@NRN%2q#o#I#IRq%2qRq%2qRq%2q%c13L3L9LST9LQR9LOP7]X5]m3L3L3L5]m7]m'p3L3]7]o'pPh%C5#7#:#R#3RoPAPfPh%C5#7#:#X#3PAPfPh%C5#7#:#8#3RPPAPfPh%C5#7#:#<#3PAPhPh%C5#7#:#7#3RfPAPhPh%C5#7#Z#7#3ROP>%1l#CRl#\RR#C#FRQ#1RT#1#\#\#\#\#\#>Pn%1\RS#8PAPXPn%0S#BRS#0PAPNPn%0\R\#8PAPBPn%0\#BR\#0PAP]Pn%1ERE#8PA%@@R@Pn%0E#BRE#0PA%EDR]Pn%8FPA%05#C#6#9#X#iRN#E1W@gRXP;PU1W@rP;PWP@PDP;%@VRV%5lRl9[UgA[WglA[Vgl%5GRG,nn%9R#A#A#A#3%5M5[n209nLRM%5LRL'hPn%0k#BPAPhPn%BYRY#0Rk#0PAPhPn%8ZPAPhPnP[PAPhPnPSPA%>H9VCnPnP\PA%`5#K#8#`#8#>PnPEPAP]PnPIPA%>FRF9VCnPnPkPA%05#J#F#K#8#>%Q5#X#A#3Rk%0T#F#J#9#A#35[@1n@G%5KRK,hXPMPLPXPKH07%NY#A#3,Wh%N5#=#A#3'h1OKf%65#:#G#9%65#:#G#6%65#:#:#=%65#:#6#:%C5#7#K#J#3%15#N#R#Z#6#`#5%15#G#_#<#G#5%B5#G#_#<#G#5%S5#7#J#J#3%05#=#6#7#6%Q5#<#9#K#3Ph%S5#7#J#F#3RKPA%EKPh%S5#7#F#<#3P>%@?R?%05#=#Z#K#7%S5#7#F#J#3%05#=#Z#F#6%S5#<#9#7#3%05#=#6#9#6%S5#<#9#X#3%05#=#6#7#8%15#=#6#=#9%Q5#<#R#R#3R>1Wh>@06F<%N5#G#:#Z#9%Q5#<#R#_#3+05%N5#G#:#6#G#5%Q5#<#R#:#3RFPhPFPA%@=%15#=#K#X#6%Q5#<#R#6#3%15#=#K#_#8%Q5#<#R#F#3R=PhP=PA%5JRJ#E%15#=#K#8#9%Q5#<#X#X#3%15#=#F#_#=%5Q9[?r1OgJ%c4RJ3M7?k3?DD3?3?DD4043M3?603i3?3?3?DDDD3?I023?7?O7?P7?o3M3M3MD;D;D;D;D;D;D;D;D;3M3M3MDDF~D;D;D;D;D;D;D;DDDDDDDDDDDDM<},kbRo;HoRP1P00RO/P0Ri/P1Rk/P1RgPkP1PiP1POP0P0P0PePdPDFYPjPmFYRm;HmRjg0085RD,P6RdP6PDP0P2PNP_P7FYR_;H_RNg00dBRe#gR?%g4Rr'PRQP?Pr%ce94e:PJCURJ;HJRe'TR5'TRA'T1^6aPPPA1^coPjP51^gmPNPe1^d_1^QJCbCbCbCbP0P2g00daRe1Pe2RNg00eoR5g018B3aRj7a2#jAme2jCUP0P2P8P7P9PBg0199=VC^Ce=43`CU5H6g00h2g00hjPpg01:4g01:lDxg01;dRp,kb5HcPkP1PiP1POP0P0P0%vp%yp%zpFY%up%{pFY=HgmP6PDP0P2g01<\9aN5R59ae2RN#jAme25%|N,t:FY=Hd_P?Prg01=TRrg00n=R?g01>Mg0101P:I00g01?FP4P4201r?g011bCs'rCU=HQJ'T'T'T'Tdo"). Qed.

Lemma f_itin :
  (s_pc (fst (fst f_r1)), snd (fst f_r1), s_log (fst (fst f_r1))) = (0x2f80c%Z, [], [])
  /\ (nth 1 f_sr1 (ELit 0), nth 10 f_sr1 (ELit 0), nth 2 f_sr1 (ELit 0), nth 4 f_sr1 (ELit 0))
     = (ELit 0x17814, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x49840)
  /\ kn_vars_lt 39 f_kn1 = true /\ kn_acall f_kn1 = f_kn2i
  /\ (s_pc (fst (fst f_r2)), snd (fst f_r2), s_log (fst (fst f_r2))) = (0x2f4d4%Z, [], [])
  /\ (nth 10 f_sr2 (ELit 0), nth 2 f_sr2 (ELit 0), nth 4 f_sr2 (ELit 0)) = (ELit 2, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x49840).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3g00:Wj1fTg00;7j2XTg00>Rj1dTg00?Rj4@Tg007<j3;Tg007Vj19Tg00<<j1bTg004Gj10Tg00\3j1\Tg00@Tj1MTg00A]j3`Tg00;Wj11Tg002oj15Tg00Bfj2iTg00D1j3gTg00E<j2pTg00FGj2QTg00GQj4xTg00Igj3wTg00H\j2OTg00L]j2ATg0000j2WTg00M8j4[Tg00MSj3_Tg00N0j1lTg00O7j3mTg00Uij1hTg01@?j2sTg01AFj1rTg00\Qj3eTg00?2j3CTg01BAj4kTf0R0#0#1#1#1p=N%10#1#0#0p=4%00#0#0#0p=3%00#1#1#0p=L%00#5p=o%00#1p=Z%10#1#1#0p=E%00#1#0#0p=6%50#Mp=Jg00]\R1P1f1R2P0C@p=af2R3P1P2P0C@p=U%00#0#1p=R%00#0#1#1p=8%10#0#0#0p=:%00#0#0#5p=2%10#1#0#0#1#0p=G%10#0#1#0p=7%00#1#0#1p=F%90#9p=j%10#0p=T%10#0#0#1p=B%10#1#1#1p==%00#0#1#0p=>%10#0#1#1p=Y%10#1#1#1#1#1#1#1p=S%10#1p=q%00#0#0#0#0#0#0#0p=D%00#0p=]%\0,Q2p=zf3R4/Q3?e20p=y%10#1#0#1p=K%10#0#1p=I%52/O0p=vg00^eR5AC5207C3p=V%03#5/O2=C50p=<f4R6/Q4?e32=C50p=?1O32=C50p=u%02#5,O3=C50p=t1O641O32=C505C5p=n%\4,Q6?e32=C50p=HP1P2g01B]P0Ckp=^%90#9#9#9p=PP1P2g01CUP0Ckp=cg0095R0g00`0R2#fR3'XR6g01DMR4#fR7'XR8P6P7P0P3g009SR9#N#4#3#L#o%d2R2C@%d4R4C@R:;;:1X11R;/X1R</X1R1%Z9#E#3#Z#6#Jg00:8R=#9R>#9R?#9R@#9RA#9RB#9RC#bRD'ag00cVRE%b=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#\#M3`5U;%R9#8#3#:#2RM#MRN5U<RO;;ORPg0085RQg008URR;;RRS%f5RTg00c8RU#MRV%G9#7#F#2RW%jCRC%T9#B#=#3#:#JRXPV%G9#7#L#2PCPXPV%G9#7#:#2RYPCPXPV%G9#7#8#2PCPVPV%G9#7#>#2RXPCPVPV%G9#Y#>#2RZPA%19R[#1R\#1R]#=#SR^#q#=R_#1R`#1#S#S#S#S#S#J%5IRI,i=%3^#D#D#D#2%0L#3RL#3R^#0#]#3Ra#0#3#D#D#25g=1z=aRb%5aRa'pP=%0]#]#\PCPVCyP=%]\R\#0R]#0PCPVP=%0[R[#:PCPVP=%0[#]R[#0PCPVP=%1FRc#:PC%JJ9`E=P=%3cPC%Z9#K#:#Z#:#JP=%:GPC%JFRFP=PKPC%JHRH9`E=P=P]PC%09#E#=#K#:#J%I9#L#D#2R]%0`#=#E#3#D#25gD1iDIPbPa1QDU%5^R^Cx%T\#D#2,QV%T9#6#D#2'pP^PX%G9#7#6#2PW%49#7#B#4%49#7#7#6%49#7#4#7%G9#K#E#2%19#T#F#Y#4#Z#5%19#B#N#8#B#5%]9#B#N#8#B#5%R9#>#E#E#2%09#6#4#>#4%I9#8#3#K#2PV%R9#>#E#=#2RWPC%MWPV%R9#>#=#8#2PA%bBRB%09#6#Y#K#>%R9#>#=#E#2%09#6#Y#=#4%R9#8#3#>#2%09#6#4#3#4%R9#8#3#L#2%09#6#4#>#:%19#6#4#6#3%I9#8#F#F#2RW1QVW?wH?%T9#B#7#Y#3%I9#8#F#N#2'v%T9#B#7#4#B#5%I9#8#F#7#2RHPVPHPC%b@%19#6#K#L#4%I9#8#F#4#2%19#6#K#N#:%I9#8#F#=#2R@PVP@PC%5LRL#M%19#6#K#:#3%I9#8#L#L#2%19#6#=#N#6%59%5_5gB1OUL%d53V7<]3<D?3<3<D?3u3V3<5tM3<3<3<D?D?3<Dn3<7<Z7<YDn3V3VDHDHDHDHDHDHDHDH3V3VD?D?D?D?D?D?RY;;YRZP6P7P0P3%N9#7#L#7#oP2C@P4C@R4=;84R2%\[#M9`E=,aF=U;NRN=;<NRF'AR='ARE'AR['A1W8:PPP[1W1OPSPE1WQRPZP=1WTYP2PF1W841W<NC[C[C[C[C[P6P7P0P3g00daRF1XF3R2g00eoRYg01EX3_R=7_3RZ#lAmF3=C@%hZC@=;8:1^>V%jCRC/^V'a1^?V5U;1^AV5U<=;1O%9C#P#P#P#P#P#P#Pg01FORO's=;QR%rOg01GG5;TP6P7P0P3g01H@9_2YRY9_F3R2#lAmF3YC@%h2C@=;841cCV1c?V'a1cAV5U;=;<N'A'A'A'A'Ado"). Qed.

Lemma h_itinK :
  (s_pc (fst (fst h_rK)), s_log (fst (fst h_rK)), s_next (fst (fst h_rK))) = (0x178e8%Z, [], 48%nat)
  /\ paylen_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 7) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6))
  /\ pay_x = EAlu ALU_ADD (EAlu ALU_ADD (EVar 6) cfglen_x) (ELit 6)
  /\ (sr_mismatch r_rvl idb h_srK sr_R 0, kn_missing h_knK (map (kmap r_rvl idb) kn_R)) = ([], []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Hdr_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g00:Wj1<Tg00;7j2?Tg004Gj10Tg00;Wj13Tg002oj1=Tg00>Rj1ATg00?Rj47Tg007Vj12Tg007<j34Tg00<<j1;Tg00\3j1GTg00@Tj19Tg012Zj4FTg013cj3BTg00A]j3>Tg00L]j28Tg0000j2:Tg00M8j4@Tg00MSj3ETg00N0j1NTg00Uij1MTg01I7j1LTg00X8j5KTg00YEj2HTg00ZKj4ITg00Zgj2JTf0R0#0#0p=C%20#2#2#2p=1%20#2p=D%00#0#0#0#0#0#0#0p=6g00cVR1f1;>0p=5g0095R0g01DMR2#<R3'?R4g00dBR5'?R6P4P5P0P3g009SR7#0#3#3#3#3#0#C#3#3#3#0#3#0#C#=%A2C7g00:8R2#2R8#2#1R9#2R:#D#1#1#1#1#1#1#1#1R;#2R<#D#1C7R=;4=g00]\R>%;:R:g0176R?%G7#9R@g015^g016J%07#6#6#6#6#6#6#6#=#9g008UP2P8%;<CF5B?%37#0R7#C#3#=#93>g017bP2P8%;;CF3>R;3B'5%G7#9R8'5R<;4<RA%;9R9/5;%=7#9R7'5R;=4>;RB%<5RCg00^eRD#<RE'?RFPCPE%A5%ADC7RG;4GRH'8RI'81:6=PAPI1:><PBPH1:>;1:FGC@C@C@P4P5P0P3g00daR3g00`0#<R01?30g00eog01J@3E3ER0#N%M0C7%L0C7=46=g01K7g0199R=9B?@,5:/5854>g01L2A>19=/5754>PCPEg01LjREg00n=RCg01Mbg01NZP2DKg01OQPDPD1HECg01PICI'JC7=4FG'8'8'8do"). Qed.
End VP1.
