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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23OpenFail_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23Open_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic3and00C47Corelib5Lists7ListDef3nthI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Open_defs5o_srBC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23Open_defs4o_rBC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS2 : list Z := (0xfa4b4 :: 0xfa374 :: 0x62fbc :: STOPS)%Z.
Definition run2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS2 scr ss [].

(* [comment removed for export] *)
Definition o_srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition o_ssB0 : sym_state := SS 0x10ab50 o_srB0 [] knA 38.
Definition o_rB := Eval vm_compute in run2 scr0 o_ssB0.
Definition o_srB : list expr := Eval vm_compute in s_regs (fst (fst o_rB)).
Definition o_knB : list kentry := Eval vm_compute in kn_after o_rB knA.

Section VP1.
Lemma o_itinB :
  (s_pc (fst (fst o_rB)), snd (fst o_rB)) = (0xfa4b4%Z, [])
  /\ (nth 10 o_srB (ELit 0), nth 1 o_srB (ELit 0), nth 2 o_srB (ELit 0), nth 3 o_srB (ELit 0))
     = (ELit 65536, ELit 0x62b70, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800).
Proof.
ltac2:(KReplay.run1 (kr_t_O23Open_defs ()) ["VP1"] "p;1p;2p;4p;3g0000j1HTg000Pj27Tg0010j10Tg001Uj1:Tg0023j1@Tg002Sj43Tg0033j39Tg003Mj12Tg0042j16Tg005;j1GTg006Dj1FTg006bj3ETg007kj2>Tg008Ej4CTg008`j3<Tg009=j1BTg00:Dj3ATg00:aj11Tg00;@j2?Tg00;[j4DTf0R0#2#0p=4%20#2p=8%00#2p==%20#2#2#2p=5g00<7R1f1g00=@P0CDp=;g00>;R0g00>YR2#HR3'7R4P0P3g00?fR5#0#0#0#0#4#8#=#4#4#0#4#8#:%@2C3R2;921711R6/71R7/71R8P7P1P6P1P1P1%55R9#2#8R:#2#5#5#:#6%05#8#4#4#4#0#4#0#0#5#:#6C3g00@Kg00A7R5#G%F:#63EC3%=9#8#5#5#:#6C3R9;991>421>89CCP0P3g00AVR01703g00Bdg00D03<R:7<3#BAA03:C3=942P7P1P6P1P1P1%15R5#1R1#1R6#1#1#1#1#1#1#1g00Dj#6R7';1;57C31;17C31;67C3=989'?do"). Qed.
End VP1.
