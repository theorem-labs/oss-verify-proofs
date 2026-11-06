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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23OpenFail_defs O23Open_defs O23Oom_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23DirRead_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3nthI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23DirRead_defs6d_srR0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23DirRead_defs6d_srR1C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes3nat01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23DirRead_defs5d_rR0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01c59OSSVerify5KrLib3O23?O23DirRead_defs5d_rR1C1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPS3 : list Z := (0x62d48 :: STOPS2)%Z.
Definition run3 (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS3 scr ss [].

(* [comment removed for export] *)
Definition ok_sr : list expr := sr_after_call_j o_srB KEPT_AL 38.
Definition ok_kn : list kentry :=
  KRange (EVar 48) 0x145000 0x7fffff7f0000 :: KAlign (EVar 48) 16 :: KWr (SA (EVar 48) 0) 65536
  :: KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 48) 0) 65536 :: kn_acall o_knB.

(* [comment removed for export] *)
Definition d_ssR0 : sym_state := SS 0x62b70 ok_sr [] ok_kn 70.
Definition d_scrR0 : scripts := SCR [false] [] [].    (* [comment removed for export] *)
Definition d_rR0 := Eval vm_compute in run3 d_scrR0 d_ssR0.
Definition d_srR0 : list expr := Eval vm_compute in s_regs (fst (fst d_rR0)).
Definition d_knR0 : list kentry := Eval vm_compute in kn_after d_rR0 ok_kn.

(* [comment removed for export] *)
Definition d_srR10 : list expr := sr_upd d_srR0 (ridx 10) (ELit (2 ^ 64 - 21)).
Definition d_ssR1 : sym_state := SS 0x10ab50 d_srR10 [] d_knR0 70.
Definition d_rR1 := Eval vm_compute in run3 scr0 d_ssR1.
Definition d_srR1 : list expr := Eval vm_compute in s_regs (fst (fst d_rR1)).
Definition d_knR1 : list kentry := Eval vm_compute in kn_after d_rR1 d_knR0.

Section VP1.
Lemma d_itin :
  (s_pc (fst (fst d_rR0)), snd (fst d_rR0)) = (0x10ab4c%Z, [])
  /\ (nth 17 d_srR0 (ELit 0), nth 10 d_srR0 (ELit 0), nth 11 d_srR0 (ELit 0), nth 12 d_srR0 (ELit 0))
     = (ELit 63, ELit 3, ELit 0x113a59, ELit 65536)
  /\ (s_pc (fst (fst d_rR1)), snd (fst d_rR1)) = (0x62d48%Z, [])
  /\ (nth 2 d_srR1 (ELit 0), nth 3 d_srR1 (ELit 0), nth 4 d_srR1 (ELit 0), nth 18 d_srR1 (ELit 0))
     = (EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x10800, ELit 0x123d20, EVar 2).
Proof.
ltac2:(KReplay.run1 (kr_t_O23DirRead_defs ()) ["VP1"] "p;1p;2p;4p;3g0000j1MTg000Pj2?Tg0010j16Tg001Nj1JTg001nj4<Tg002Nj33Tg002hj1=Tg003Mj18Tg004Vj12Tg005;j1ITg006Dj1LTg006bj3KTg007kj2>Tg008Fj2BTg008`j4ETg009;j3@Tg009Xj1HTg00:_j3GTg00;<j15Tg00;[j4FTf0R0#2#2#2#2p=:%=0#2p=1%=0#=p=9%20#=p=4%20#2p=0g00<7R1P1f1R2P0C<p=Df2P1P2P0C<p=7%50#5p=;P1P2g00=@P0CFp=AP1P2g00>?P0CFp=Cg00?>R0g00?\R2#MR3'?R4P0P3g00@iR5#:#1#1#1#9#4#0#9#0#6%J2R2C<R6;361?11R7/?1R8/?1R1%=5R9#9#9#6#8%69#8'D%05#4#0#9#1#1#4#4#1#4#6#8577%:5R9#2#0R:#2#:#:#6#8578R;;3;R<P0P3%15#0#1#9#4#4#0#1#0#6P2C<R2=342R=g00ANg00B:R>#I%L:#83K%19#0#:#:#6#8'D%05#1#0#9#9#4#0#1#:#6#8577%;>R>#I578R5=315R9'>R:'>1B46P<P:1B1;P=P91B421B15CECECEP0P3g00BYR91?93R=g00CgR:g00E33@R<7@3#HAG93<C<=346%5>R6#5R<#;#;#;R?#5R@#5RA#5#;#;RBg00F1#8RC'A1A?C'D1A@C5771AAC578=31;P0P3g00FO9@=:R:9@93#HAG93:C<=3421C>C1C6C'D1C<C577%5B/CC578=315'>'>'>do"). Qed.
End VP1.
