(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr05K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr04K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I47Corelib7Numbers7BinNums1Z00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rG3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2PXC5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_datac5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4srG3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4knG3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4scG3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rH3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4srH3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4knH3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4scH3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rI3c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rF4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4srF4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4knF4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4scF4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rG4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rH4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4srH4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4knH4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4scH4c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3rI4K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond06K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rAc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rBc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rCc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rDc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rEc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rFc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rGc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rHc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3srHc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3knHc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs4scOFc5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs2rI".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x11e154; 0x11e6d4; 0x11ec28; 0x11e058; 0x12a64; 0x12bf0; 0x10fefc; 0x10e4e0; 0x1139cc]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
(* [comment removed for export] *)
Definition sc_of (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
(* [comment removed for export] *)
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition IHI : Z := 0x159000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x63140 sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x11eff4 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB := Eval vm_compute in run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x1143c4 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x1143c4 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x115280 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x1143c4 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x1143c4 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x1143c4 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x114be0 srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rG3 := Eval vm_compute in run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 : stdio_res := Eval vm_compute in sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3.
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3 := Eval vm_compute in run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 : stdio_res := Eval vm_compute in sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3.
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0x114be0 srI30 [] knI30 263.
Definition rI3 := Eval vm_compute in run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3)).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition rF4 := Eval vm_compute in run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 : stdio_res := Eval vm_compute in sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4.
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4 := Eval vm_compute in run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS 0x1143c4 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x114be0 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Section VP1.
Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0x1139cc%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x114db0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x1b8d4, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x1139cc%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x10e4e0%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0x1139cc%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x1157d0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x1139cc%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x10e4e0%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23OpenFail_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10\Tg000Pj2tTg0010j1BTg001Nj1?Tg002Wj12Tg0036j1GTg004?k30QTg005Hj11Tg005mj18Tg006Kk10@Tg006kj3>Tg007Ek10VTg007gj10Tg008Lk30;Tg009Uj3qTg00:`j2NTg00;jk40ZTg00=3k20ATg00>>k20NTg00?Ik40MTg00@Tk30WTg00A_j2TTg00Bjm<07Tg00D3j2_Tg00DUk40ITg00E^k406Tg00Fkj2=Tg00GFj2\Tg00G`j3]Tg00H=j1kTg00IDk503Tg00JLk108Tg00KPk10<Tg00LRk102Tg00MUk10:Tg00NXk105Tg00O[k10GTg00P]k109Tg00Q_k30=Tg00Rhj4lTg00SHj35Tg00Shj3uTg00U3k40FTg00UNk30[Tf0R0#0#0#0p=<%10#0#0#1p=:%10#1#0#0p=4%10#1#1#0p=O%00#1#1#0p=K%00#8p>0?%20#2#2p=~%20#2p>0H%20#2#2#2p=e%20#2#2#2#2#2#2#2p>01%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=f%80#?p=Ig00UkR1f1R2<0=0p=cg00VWS00g00W7S01P2P0H06p>0Bg00WiR3?520p=xg00Y6R4f2R5P2P0Clp=J%00#0#1#0#0#1#1#1#1p=R%10#0#0#0p=7%00#0#0#8p=9%00#0#1#0p=A%10#0#1#1p=w%00#0p=;%?0:0=12p=`%10#1p>04%10#0p>0R%00#0#1#1p=D%00#1#0#1p=v%00#0#8#?p=Z%00#Bp>0E%00#1#1#1p=Q%00#0#0#0p=3%10#0#1#0p=L%10#1#1#1#1#1#1#1p={%10#1#1#1p=EB0;120p=s%10#1#0#1p=rg00YTR6%G2;50p>0D%G5%G2=560556p=Hf3R7%G2=5609565556p=zf4R8A562095659567556p=[%G7A56209565556p>0C1N75?u20p=S%05#B,N7?u20p=M%10#0#0p=y%00#1p>0P%00#1#0#0p=@%00#0#0#1p=Y%10#8p=p%?09u52p>0O%00#1#0#1#1p=X%00#0#1p=b%00#0#0#0#0#0#0#0p=a%00#0#0#0#0#0#0#8p>00%B0,N2p>0Y%00#0#1#0#0p>0X%82/T0p>0L%00#0#1#0#0#1#1p=d%00#1#0p=og00Z]R9A5920755p=m%05#8%02#0#0#8'T=590p=g1N87?u52=590p=C%05#8/T2=590p>0K1T52=590p>0U%02#8,T5=590p>0J1T871T52=590559p>0T%08#8/T7%05#8/T2=590559p>0>A5920959595979598p=F%B7,N8?u52=590p=6%17#0#0#0#B,N8?u52=590p=P%07#B,N8?u52=590p=VP4P4P2P0Clp=iP5P4P2P0Clp=jP7P6P6P6P5P2ClP0Clp=WP5P6P2P0Clp=}A5920p>0Sf6R:f5R;P8P7P5P2P0H0FH0Fp=|P8P71\52P0H0Fp=^g00[hR<?]20p=hB0[<20p=nA>:;8A>752/=0'=p=U&0\3R0,t4R7g00]6R5#<#:#4#O#K$0?R2g00][S02%B5#?S03g00^GR;#2R:#2R8#2R=#2R>#2R?#~R@$0H#e$01#fRA#~$01#f#f#f#fRB#GRC40Q%15RD#1RE#1RF#1RG#1RH#IRI'c%85S04#?RJ+0B&0@3R3'x5J0RK;>Kg00^fRL$0VRM%R5#:#7#9RN%05RO#8RP%05#A#:#w#K#9RQ%G;RR%0ORS#0RT#1RU#1RV#0S05#;S06#0RW#BRX'`RY1cRC%0TRZ#1R[#1R\#1R]$04#B#?R^'cS07PY%1ORO#0R_#0R`#0S08#0Ra#IRb&0R5#O#D#v#ZRcPJ&0EWRW,`RRd&0HB#e#f#f#fS09#2#eS0:#2S0;#2S0<#eS0=#2S0>#2S0?#2S0@#2S0A#2S0B#2S0C#~$01S0D#2S0E#2S0F#2S0G#2RB%?QS0HPd%0[R[#;S0I#;Re#0Rf#<#ZS0J%05#Q#3#D#L#9Rg#?S0K%2B#eRh%2hRh%2hRh%1SRS#0Ri#1Rj#IS0L%1HRk#1#{Rl#1Rm#1#ERn#1#{Ro#IRpPJ%ehRh#G%2hRh%2hRh%2hRh%2hRh%2hRh%2hRhg00_oRqg00`[Rr#?Rs1sCsRt'sS0M%IUS0N'sRu80;pS0OPu%?NRv%w5#7#r#v#IS0PPJPcPs1stsS0QPJPt%~h$01Rh%2hRh%2hRh%2hS0R&0@6Rh+0D3HCzD[D[3H3H3HD[3HCzH0CPs%R5#:#4#9S0SP@%<FS0T#0S0U$0E,`RS0VCSS0WPs%R5#:#r#9P@PYCSS0XPs%R5#:#E#9S0YP@PYCSS0ZPR%0URU#1RF#1S0[#;P@PsCMS0\PR%0URU#0S0]#0S0^#0RwP@Q0MCMS0_PR%<FRFP@PCCMS0`PRPWP@%1f#L#ICSS0aPR%yUP@PsCMS0b%8m9qCrS0cPR%<HP@%G8RHCMS0dPR%0iRi#0S0e#0S0f#0S0g#0S0h#BRmP@%1_RU#0Rf#;RW#BS0i,`RCSS0jPR%BwP:%0ZRw#IRxCSRyPR%BFP@%0DRD#1RF#1Rz#y#4R{#1$0P#Q#3#K#E#A#3#Q#@#K#E#K#O#ICSR|1NRXS0k%;{#w#Y#:#3#Y#r#D#@#w#K#D#Y#p80O@R{PR%;]P@%1o$04Ro#;#4#4#4#4#4#4#r#ICMS0lPR%<\P@%1o#E#{Ro#0#{#{#ICMS0mPR%;kP@%0DRD#1Rk#1#D#D#D#D#D#ZCMS0nPR%1wR\#<P@%<jR]#7#:#ICMS0oPR%1U#3P@Q00P8PrP@H0ZRUPR%0wRw#;S0p#;RX#BP@%X5#3#7#7#9R}#?R~CSS0qPR%ywP@PsCMS0rPR%y\P@1`RmRmCMS0sPR%y[P@Q0VCMS0VPR%BeP@%1SRS#1Re#<R[#BS0t,`RCSR\PR%yfP@PsCMPR%;WP@PsPR%1`R`P@PsPR%3`P@PsPRQ08P@PsPR%0aR`#;P@PsPRPeP@%IORePRP[P@&0P5#K#A#A#4#ZS08PR%0SRSP@PJPR%;SRS#0R[P@P~PRPjP@%w5#7#4#Y#IPRP]P@PvPR%1iS0u#<S0vP@%;5#v#A#E#3#ZPs%R5#:#L#9P@PsPs%R5#:#:#9RiP@PsPs%R5#L#:#9RjP>%1o#ERo#1$04#{#pRW#?Ps%R5#L#@#9P@PbPs%R5#L#D#9RfP@PYPsPNP>PePRQ0gP@PsPRP]P@PsPRP[P@PsPRQ0tP@PsPRQ06P@PsPR%1VS06#<S0tP@%1ORO#<RV$0ER[,`RR]PRQ0^P@PUPRQ0IP@PsPRQ0pP@PsPR%<GP@1cRxRxPRQ0UP@PHPR%0EREP@%?PRGPR%;ERE#0ReP@P~PR%<zP@%;5#@#O#E#K#ZPR%<FRFP@P]PR%<kRkP@PUPRPSP@PsPRP`P@PsPRQ0iP@%GARAPRP[P@PHPRQ0]P@%IEPRQ0fP@PsPR%0DRD#;R[P@PGPRPOP@%75#4#O#:#ZPs%b5#4#3#:#K$0?P>1sAs:0;qs%al#a#a$00Rl%;XRX#3Rq#<#3RO#0RS#7#3#a$00RU5qH%<o#a#p=qAWPRQ0TP@PsPRPeP@PsPRPFP@PsPRP[P@PsPRPVP@PxPRPaP@%75#4#v#3#ZPRQ0eP@PGPRPwP@%8TRT#?Rw,cRPRPEP@%;5#D#Q#4#7#Z%8ZRZ-0AR%aS#a$009qRl20YRORS%8ORO+0NPRPrP@PGCSPRPTP@%G:PRPZP@PHPR%8DP@Ps%G=R=?qlU%G>RD?qlUPSPO1N=r%8`H0MPSPO1NDrPZH0M20A=T20ADT&0X5#O#3$00,Ns%<k$00+0N20LqN%d5#O#K#APi%d5#O#K#4Q0S%d5#O#Q#7Q0Y%d5#O#7#3Pf%d5#O#:#@Pj%d5#O#L#K%R5#r#7#9%d5#E#K#3#p%d5#E#7#@#pRjPj%b5#w#E#7#@#pRj%b5#4#3#7#3%b5#4#3#E#@%X5#3#D#EPs%05#Q#3#A#Y#9RfP@%?fPs%05#Q#3#A#v#9P>%G?R?%b5#4#3#:#L%05#Q#3#D#3%b5#4#3#4#@%05#Q#3#D#@%b5#4#3#r#@%05#Q#3#D#7%b5#4#3#E#3%o5#4#Y#3#71Ns}@0Ww8%v5#7#@#@#7%X5#3#7#L#9+0L%o5#4#A#D#3#p%X5#3#7#r#9RwPsPwP@P=%o5#4#A#D#7%X5#3#7#E%o5#4#A#@#@%X5#3#:#A#9R=PsP=P@%8XRX#?%o5#4#A#@#4%X5#3#:#:%o5#4#A#K#7%X5#Y#Y#3%o5#4#@#@#7%X5#A#aQ04%8n5q?1TrX&0@93m3g3g3gDC40K3gDC40U3m80K}60Jg3g3g3gDCDC3g60JjI0TI0>I0>I0>DFDFDCDCDCDFD6D6D6D6D6D6D6D6D63mDCDPDVD6D6DCDCD6D6D6DVD6DVDPD6D6D6D6D6D6D6DCD6D6D6DCDCDCDCDCDCRjD6DVDPDVDPDVDPD6DPD6DPD63mDFD63mDFDFDFDFRgN<07,_LR};>}R91t44RX/t4R41iQN=jXPRQ;>QRr1t66R?/t6Rn/t6R=P?PYQ07PcCW=}nJRw;>wR8AJ023Rf=>7fRiPNPP%05#A#:#Q#4#9RqPYPYPYPbPsPsPmQ0R#2Rk%?qPmQ0JQ0K%2k#eRD%2DRD%2DRDPv1sJuPs%eDRD#G%2DRD%2DRD%2DRD%2DRD%2DRD%2DRDP~PJQ08PsPsPsPsPsPsPs%~D$01RD%2DRD%2DRD%2D00Dh3HCzD[D[3H3H3HD[3HCzH0CRDQ0WQ0XQ0ZQ0\Q0_Q0`Q0aQ0bQ0cQ0dQ0jPyQ0lQ0mQ0nQ0oQ0qQ0rQ0sQ0V20S\jDFDFRj9m|{DFDFDFN<07,_LR{=>M{R\1iqN=jXPR~=>4~RTP?PYPYPsCWRZ=>nZRO%05#Y#4#:#4#9=J03RS=>7SR`20BICg00a9RUg00aYRlPUP;P>PCH0IQ0QH06/x3'x9J02RG=>7GREPNPP%05#A#L#E#L#9RaPY1cR^RxPYPbPHPCPdQ09%?aPdQ0JQ0KQ0:Q0;Q0<Q0LPpPCQ0=#GQ0>Q0?Q0@Q0AQ0BQ0CPsQ0NPvPcPsPHPsQ0QQ0MPtQ0DQ0EQ0FQ0G00Dh3HCzD[D[3H3H3HD[3HCzH0CPgN<07,_LRg=>MgRh1iaN=jXPRa=>4aRtP?PYPxPHCWRH=}nCRC=>=CRx%<5#E#3#L#L$0?=J03R5=>75RdPNPPPqPYQ0[$04#B,`RRqPYPbPsPsPmPDQ0WQ0XQ0ZQ0k%8_80O:PRQ0uP@Q0PPRQ0vP@PvPRQ0eP@PuPRQ0hP@Q0OPRQ06P@PpPRQ0tP@Q0LPRQ05P@Q0HQ0\Q0_Q0`Q0aQ0bQ0cQ0dQ0jAmy|jDFDFDPDVDPDVDPDVDPDFN<07,_LRj=>MjR|P?PYPqPsCWRq=>nqRy/=`R@,=TRp'=Ru,=iRv'=R:'=R_'=RD'=Rm'=Rb'=RP'=RN'=RV'=R['=RF'=Re'=RA'=P7PKP9PAPMP}PrPeP4PQP8PFP=PwPiP[1\7fR[P\PV1\M{PTPN1\4~RNPOPP1\nZP`Pb1\7SRbPEPm1\7GPhPDPMPgPtP_P4PaPxP:P=PCPdPvP7P5PiPuP[P|Pp1\MjPTP@PNPyP`1\nqPbF|F|D^D^D^D^F|F|F|D^D^D^D^P71t<0R<g00bKRbg00cW3]R`,h0#k1n0`5J0Q02Q03g00dTR`40Q/cI00BJ/x39J02PMg00ePRyg00fKRNPBg00gHg00hFI03g00iDRB,_LP4&08B&0<B'i&02B5jXPQP=P?&0:B&05B&0GBCW&09B5}nP?PYB0=1R`/c^PcCW=}nJP7g00jB9]<bRJ,h0#k1n0J5J0PfPMPyPNPkg00k?g00l=I03g00m;RJ,_LP4&08J&0<J'i&02J5jXP~PnP?&0:J&05J&09JCWPZP7g00n99]<bRZ,h0#k1n0Z5J0PSP7g00o69]<bRZ,h0#k1n0Z5J0Q00Q01PIP`H06PUPlPUP;P>P`H0IB0;1`s/ssH06/x3'x9J02PMPyPNQ09g0103g0111I03g011oR2,_LP4&082&0<2'i&0225jXPaP=P?&0:2&052&0G2CW&0925}nPnP6PHP`ClP7g012m9]<bR`,h0#k1n0`5J0P5P7g013j9]<bR5,h0#k1n055J0PfPMPyPNPkg014gg015eI03g016cRk,_LP4&08k&0<k'i&02k5jXP~PnP?&0:k&05k&09kCWPqg017a9]<bRb,h0#k1n0b5J0=>7SFUFUFUFUFUFUFUFUFUdo"). Qed.
End VP1.

Section VP2.
Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x11eff0%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x11e154%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x11e154%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x11ec28%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x11e154%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x11e154%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x11e154%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x1139cc%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x114be0%Z, 0x127cc0%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x10e4e0%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_V23OpenFail_defs ()) ["VP2"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10STg000Pj2kTg007gj10Tg006Kj1uTg006kj3ATg002Wj12Tg0036j1HTg001Nj18Tg005Hj11Tg00E^j4dTg00:`j2GTg018^j4~Tg00DUj4{Tg0010j1VTg004?k30=Tg005mj17Tg007Ek10RTg008Lj3qTg009Uj3bTg00;jk40QTg00=3j2vTg00>>k206Tg00?Ik405Tg00@Tk30NTg00A_j2UTg00Bjm<0KTg00D3k200Tg00Rhj4QTg00Fkj2FTg00GFj2}Tg00G`j3LTg00Q_j3sTg00IDk50GTg00JLk10FTg00KPk10ETg00LRk10DTg00MUk10CTg00NXk10BTg00P]k10ATg00SHj3;Tg00Shj3eTg00U3k40>Tg00H=j1|Tg00UNk307Tf0R0#0#0#1#1p=>%10#1#0#1p=`%10#1#1#1p=B%10#1#1#0p=I%00#0#0#7p=:g00Y6R1f2R2f1R3P0CQp=J%00#0#0p=<%00#0#0#0p=3%10#0#1#0p=K%00#7p=z%20#2p=p%20#2#2#2p=r%20#2#2#2#2#2#2#2p=x%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>09g00UkR4?q30p=a%10#1#1#1#1#1#1#1p=h%10#1p>03%00#0#0#0#0#0#0#0p=\%10#7p=gg00WiR5?;30p=M%10#0#0#0p=6%00#1#0#1p=f%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=lAs430p=E%70#8p=Sg00a9R6g00W7S00P3P0Cdp=y%10#0#0#1p==%10#1#0#0p=4%00#1#1#0p=@%00#0#1#0#0#1#1#1#1p=T%00#0#1#0p=C%00#1#1#1p=N%00#0p=D%00#Vp=j%00#0#7#8p=_%00#1#0#1#1p=Z%00#1p>0<g00YTR7%H2%H3=;703;p=iA;7309;72p=Y%H3=;70p>0;%10#0#1#1p>0:f3R8/G2?e30p>08%00#1#0#0p=?%00#0#1p=W%00#0#0#0#0#0#0#7p=o%V0,G3p>0P%00#0#1#0#0p>0O%73/U0p>04%00#0#1#0#0#1#1p=^%00#0#0#1p=n%00#1#0p=cg00Z]R9A;9307;2p=R%02#7%03#0#0#7'U=;90p=]f4R:/G8?e23=;90p=9%02#7/U3=;90p>021U23=;90p>0M%03#7,U2=;90p>011U:81U23=;905;9p>0L%0:#7/U8%02#7/U3=;905;9p=t%V8,G:?e23=;90p=5%18#0#0#0#V,G:?e23=;90p=O%08#V,G:?e23=;90p=X%V8,G:%73#87e2=;90p=mP7P7P3P0CQp=wP:P81}23P0H0>p=Pg00[hR;?L30#|p>0@B07;30p>0HP1P8P2P3CQ=A:0p>0?AA823/F0p>0If6R<f5R=;A:AA823/F0'Fp>0Jf7P1P<AL;=:#|B07;82CQ;A3/F0p=[&0S5R0,k1R3g00]6R8#0#>#`#B#I#:%u5R55J0R2;A2%<8#B#3#K#K#zR=g00VWR:g019kg00^GR<#2R>#2R?#2R@#2RA#2RB#2#pRC#p#r#x$09RD#HREg00`[RF#8RG'aRH%18RI#1RJ#1RK#1RL#1RM#1RN#1#hRO#1RP#1#BRQ#1#hRR#1$03RS#1#B#hRT#1#BRU#<#\#gRV#8Cd/M55J0RW=A3WS01AJ0=5RX=A3XS02%08#>#`#6#f#:=J05RY=A3YS03P:g01:]S04%2D#p#x#l#lRD#HRZ/aGR[PZCd%H?R\/EZ/GFP>P:PGC~/M5'M9J0=R]=A3]S05%SMR^/yZP6g00aYS06P6P<PAPZC{1a[GCd/M5'M9J0=R_=A3_S07g00][S08%V8#8S09<0=Z/E^%78R`#8Ra'y/M59J0=Rb=A3bS0:%<8#=#4#I#@#z=J05Rc=A3cS0;g00^fRd$0RS0<%T8#=#6#:Re%08Rf#7Rg%08#C#=#N#4#:Rh%H<Ri%0fRj#0Rk#1Rl#1Rm#0S0=#DS0>#0S0?#VS0@#8'ERn1EiZ%0kRo#1Rp#1Rq#1Rr#1#j#8Rs'ERtPn%1fRf#0Ru#<Rv#SS0APGPG%1jRj#0Rw#0Rx#0Ry#0S0B#0S0C#0S0D#VS0E#8,EiRz%pD#r$09#l#l#lRD%8h%0pS0F#DS0G#DS0H#0Rp#<#_%08#N#3#>#K#:R{#8%2D#rR|%2|R|%2|R|%8eS0I1aG[S0J%Sl'aR[,aa%r|R|#H%2|R|%2|R|%2|R|%2|R|%2|R|%2|R|%Z8#3#6#6#:R}#8R~&0<8#@#C#C#4#_%2|#p#xR|%2|R|%2|R|%2|%u73i3i9YGG9YGG9YGG7YG7Ya3i3i3i5YG3Y+0;3i3Y7Yz+0;PG%T8#=#4#:S0KPC%<KS0L#0S0M#j#8,EiRKPG%T8#=#`#:PCPnPG%T8#=#B#:S0NPCPnPi%1xRxPC&0:8#6#`#f#SPi%3xPCQ0IPiPyPCP[PiQ0DPCg00_oRx%SRRR;q[Pi%1mRmPCPRPi%<mRmPC%1wRw#SPiQ0=PC%D8#f#>#@#4#_Pi%0lRl#1RRPCPGPi%0lRl#0S0=#0R[#0R|PCQ0JPi%<RRRPCPZPiQ0?PC%1p#K#SPiPlPCPG%7P9bZFPi%<M#jPCP\H08PiQ0EPC%1u#D#jRu#8,EiPiP|P>%0oR|#SRMPiPRPC%0IRI#1RR#1RZ#1#D#4RP#1$0<#N#3#@#B#C#3#N#?#@#B#@#IPiQ0@PC%WP#@#>#C#3#>#K#@#=#@#4#@#>#SPi%<rPC%DS#4#4#4#4#4#4#`Pi%3qPC%0T#h#hPi%<NPC%0IRI#1RN#1#>#>#>#>#>#_Pi%1|RT#3PC%<wRw#6#=Pi%0|R|#DRq#DRSPCP~PiP|PCPGPiPTPCPzPiQ0FPCPKPiQ0HPC%1jRj#1#D#jRK#8,EiPG%T8#=#K#:PCPGPG%T8#=#=#:RzPCPGPG%T8#K#=#:RTPA%1U$03#h#gRU#8PG%T8#K#?#:PCQ0APG%T8#K#>#:RrPCPnPGPePA%SfPiQ0CPCPGPiPwPCPGPi%<jRjPCPGPiPKPCPGPiQ0>PCPGPiPmPC%1fRf#<Rm#jRK#8,EiRwPiP[PCP:P?PFPCH0QR[PiQ0GPCPGPiPqPCPGPi%<LPC1EiMRMPiQ0MPCP\Pi%0JRJPC%8gRLPi%DJRJ#0RqPCP~Pi%<ZPC%D8#?#I#B#@#_Pi%<RRRPCPwPi%<NRNPCP[PiPjPCPGPi%0vRjPCPGPiPuPCPEPiPKPCP\PiQ0=PCPJPiQ0BPCPGPi%0IRI#DRKPCPLPiPfPC%68#4#I#=#_PG%W8#4#3#=#@#zPAAqxGH%\O#\#\#oRO%DSRS#3Rx#<#3RH#0Rf#6#3#\#oRu5b\AbEVUPiQ0LPCPGPiPqPCPGPiPRPCPGPiPKPCPGPiPmPCPMPiPvPC%68#4#f#3#_PiPyPCPLPiP|PC%7kRk#8R|,EiPiPJPC%D8#>#N#4#6#_%7oRo,vi%\f#\#o9biO20PiHRf%7HRH+06PiPFPCPLH08PiPkPC%H>PiPoPCP\Pi%7IPCPG%H@R@?bOu%HARI?bOuPfPH1G@F%7jH05PfPH1GIFPoH051v@k1vIk&0O8#I#3#o,GG%<N#o+06204xe%^8#I#@#CPz%^8#I#@#4Q0K%^8#I#N#6Q0N%^8#I#6#3Pr%^8#I#=#?PT%^8#I#K#@%T8#`#6#:%^8#B#@#3#g%^8#B#6#?#gRTPT%W8$0:#B#6#?#gRT%W8#4#3#6#3%W8#4#3#B#?%Z8#3#>#BPG%08#N#3#C#n#:RrPC%8rPG%08#N#3#C#f#:PA%HBRB%W8#4#3#=#K%08#N#3#>#3%W8#4#3#4#?%08#N#3#>#?%W8#4#3#`#?%08#N#3#>#6%W8#4#3#B#3%c8#4#n#3#61GG}@0N|?%f8#6#?#?#6%Z8#3#6#K#:+04%c8#4#C#>#3#g%Z8#3#6#`#:R|PGP|PCP@%c8#4#C#>#6%Z8#3#6#B%c8#4#C#?#?%Z8#3#=#C#:R@PGP@PC%7SRS#8%c8#4#C#?#4%Z8#3#=#=%c8#4#C#@#6%Z8#n#n#3%c8#4#?#?#6%Z8#C#\%7Q9bB`1UFS%u93R3]3]3]D94023]D940M3R802}601{3]3]3]D9D93]601TI0LDtDtDt3R3R3R3RD9D9D93R3RD5D5D5D5D5D5D5D5D53RD9DODXD5DmD9D9D5D5D5DXD5DXDOD5D5D5D5D5D5D5D9DXD5D5D9D9D9D9D9D9D5DODODOD5DmD5DmDmD9DmD5D93RDODXDXDXDODODXDODXDOD5DOD9D9D9N<0K-00dRT;ATR{1k11R}/k1R9P}P1P1P1PhPeCQPgCQRg;AgRe1k77Rh/k7RSPhP71wntPGCQRt;AtRB%08#n#4#=#4#:=J05R8=A38R`'FRQ'FRC'FR@'FR|'FR?'FRr'FRz'FRx'FRN'FP3P2Q01PNP3PWQ02PxP3PXQ03PzP3PYQ05PrP3P]Q07P?P3P_Q0:P|P3PbQ0;P@P3PcP{PCQ0<PTPePQP9PgPBP`PSPt1}38DPDPDPDPDPDPDPDPDPDPDPP3P0P01k;0R;g00bKRtg01;O3LR`P0P`P2P3P0P0g01<K9L;tR2P0P2PWP3P0P0g01=G9L;tRWP0PWPXP3P0P0g01>C9L;tRXP0PXPYP3P0P0g01??9L;tRYP0PYP:Q04g00dTRY=q4GRXPYCdAs4\Y/GFP>P:PGC~/M5'M9J0=P3P0P0g01@;9L;tR:P0P:P6Q00P^PYCdP6Q06P6P<PAPYC{1aXGCd/M5'M9J0=P3P0P0g01A79L;tRXP0PXQ08Q09<0=Y/E^/ya/M59J0=P3P0P0g01B39L;tR=P0P=PcQ0<g00ePg00fKPDg01Bog01ClI0Gg01DiRD-00dP9P}P1P1P1&0FD&0EDCQ&0DDCQPgPSPhP7&0CD&0BD'w&0ADCQPhP7As4iY/Es,wnPGCQP3P0g01Eg9L;tRt-0@020H0tP8I0?H0IK0JG[G[G[G[G[G[G[G[do"). Qed.
End VP2.
