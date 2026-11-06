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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall O2OpenFail_defs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Open_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C47Corelib5Lists7ListDef3nthI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Open_defs5o_srBC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2;O2Open_defs4o_rBC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS2 : list Z := (0x2f94c :: 0x2f80c :: 0x17ab8 :: STOPS)%Z.
Definition run2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS2 scr ss [].

(* [comment removed for export] *)
Definition o_srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition o_ssB0 : sym_state := SS 0x37344 o_srB0 [] knA 38.
Definition o_rB := Eval vm_compute in run2 scr0 o_ssB0.
Definition o_srB : list expr := Eval vm_compute in s_regs (fst (fst o_rB)).
Definition o_knB : list kentry := Eval vm_compute in kn_after o_rB knA.

Section VP1.
Lemma o_itinB :
  (s_pc (fst (fst o_rB)), snd (fst o_rB)) = (0x2f94c%Z, [])
  /\ (nth 10 o_srB (ELit 0), nth 1 o_srB (ELit 0), nth 2 o_srB (ELit 0), nth 3 o_srB (ELit 0))
     = (ELit 65536, ELit 0x1766c, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800).
Proof.
ltac2:(KReplay.run1 (kr_t_O2Open_defs ()) ["VP1"] "p;1p;2p;4p;3g0000j1ITg000Pj28Tg0010j10Tg001Uj1<Tg0023j1@Tg002Sj42Tg0033j39Tg003Mj17Tg004Vj1HTg005_j1GTg006=j3FTg007Fj2?Tg007`j4DTg008;j3>Tg008Xj1CTg009_j3BTg00:<j11Tg00:[j2ATg00;6j1;Tg00;[j4ETf0R0#;#;p=3%;0#0p==%00#;p=4%00#0p=6%00#0#0#0p=5g00<7R1f1g00=@P0CEp=:g00>9R0g00>WR2#IR3'8R4P0P3g00?dR5#0#3#3#=#4#4#6#3#6#<%@2C2R2;921811R6/81R7/81R8P7P1P6P1P1P1%55R9#0#6R:#0#5#5#<#7%45#3#4#=#4#=#3#6#<#7C2g00@Ig00A5R5#H%G:#73FC2%=9#6#5#5#<#7C2R9;991?421?89CDP0P3g00ATR01803g00Bbg00Cn3>R:7>3#CAB03:C2=942P7P1P6P1P1P1%15R5#1R1#1R6#1#1#1#1#1#1#1g00Df#7R7':1:57C21:17C21:67C2=989'Ado"). Qed.
End VP1.
