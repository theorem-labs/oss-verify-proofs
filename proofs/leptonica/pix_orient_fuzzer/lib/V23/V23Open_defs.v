(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23OpenFail_defs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23Open_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic3and00C47Corelib5Lists7ListDef3nthI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00c5ARocqVerifyHarness?AgentSubmission3V23<V23Open_defs5o_srBI47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23<V23Open_defs4o_rBK47Corelib7Numbers7BinNums1Z01".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPS2 : list Z := (0x10e958 :: 0x10e818 :: 0x635e0 :: STOPS)%Z.
Definition run2 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS2 scr ss [].

(* [comment removed for export] *)
Definition o_srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition o_ssB0 : sym_state := SS 0x11eff4 o_srB0 [] knA 38.
Definition o_rB := Eval vm_compute in run2 scr0 o_ssB0.
Definition o_srB : list expr := Eval vm_compute in s_regs (fst (fst o_rB)).
Definition o_knB : list kentry := Eval vm_compute in kn_after o_rB knA.

Section VP1.
Lemma o_itinB :
  (s_pc (fst (fst o_rB)), snd (fst o_rB)) = (0x10e958%Z, [])
  /\ (nth 10 o_srB (ELit 0), nth 1 o_srB (ELit 0), nth 2 o_srB (ELit 0), nth 3 o_srB (ELit 0))
     = (ELit 65536, ELit 0x63194, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800).
Proof.
ltac2:(KReplay.run1 (kr_t_V23Open_defs ()) ["VP1"] "p;1p;2p;4p;3g0000j1HTg000Pj29Tg0010j10Tg001Uj17Tg002:j1<Tg002Xj1?Tg0038j42Tg003Xj3:Tg0042j16Tg005;j1GTg006Dj1FTg006bj3ETg007kj2>Tg008Ej4DTg008`j3=Tg009=j1CTg00:Dj3BTg00:aj11Tg00;@j2ATg00;[j4@Tf0R0#0#0p=4%00#7p=3%70#0p=8%00#0#0#0p=5g00<7R1f1g00=@P0C@p=;g00>;R0g00>YR2#HR3'9R4P0P3g00?fR5#0#4#3#7#8#8#3#3#3#8#4#<%?2C2R2;:21911R6/91R7/91R8P7P1P6P1P1P1%55R9#0#4R:#0#5#5#<#6%75#4#3#7#4#3#8#3#3#4#<#6C2g00@Kg00A7R5#G%F:#63EC2%89#4#5#5#<#6C2R9;:91>421>89CDP0P3g00AVR01903g00Bdg00D03=R:7=3#CAB03:C2=:42P7P1P6P1P1P1%15R5#1R1#1R6#1#1#1#1#1#1#1g00Dj#6R7';1;57C21;17C21;67C2=:89'Ado"). Qed.
End VP1.
