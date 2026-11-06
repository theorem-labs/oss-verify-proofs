(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2PXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4srH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4knH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4scH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rI3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4srF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4knF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4scF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4srH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4knH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4scH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3rI4C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib3O23@O23OpenFail_defs2rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs4scOFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23@O23OpenFail_defs2rIC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x109cb0; 0x10a230; 0x10a784; 0x109bb4; 0x12a64; 0x12bf0; 0xfba58; 0xfa03c; 0xff528]%Z.
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
Definition IHI : Z := 0x145000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x62b1c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x10ab50 srB0 [] knB0 39.
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
Definition ssC0 : sym_state := SS 0xfff20 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xfff20 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x100ddc srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xfff20 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xfff20 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xfff20 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x10073c srI0 [] knI0 263.
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
Definition ssI30 : sym_state := SS 0x10073c srI30 [] knI30 263.
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
Definition ssH40 : sym_state := SS 0xfff20 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x10073c srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Section VP1.
Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0xff528%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x10090c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x1b895, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0xff528%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0xfa03c%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0xff528%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x10132c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0xff528%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0xfa03c%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23OpenFail_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10]Tg000Pj2wTg0010j1ATg001Nj1=Tg002Wj12Tg0036j1DTg004?k30STg005Hj11Tg005mj18Tg006Kk10@Tg006kj3>Tg007Ek10XTg007gj10Tg008Lk30;Tg009Uj3tTg00:`j2NTg00;jk40ZTg00=3k20?Tg00>>k20NTg00?Ik40MTg00@Tk30WTg00A_j2RTg00Bjm<05Tg00D3j2`Tg00DUk40HTg00E^k404Tg00Fkj2?Tg00GFj2VTg00G`j3aTg00H=j1qTg00IDk503Tg00JLk106Tg00KPk102Tg00LRk108Tg00MUk109Tg00NXk101Tg00O[k10ETg00P]k107Tg00Q_k30>Tg00Rhj4kTg00SHj33Tg00Shj3iTg00U3k40DTg00UNk30\Tf0R0#1#1#1#1p=;%10#1#1#0p=J%10#0#1#0p=T%00#1#0#1p>0:%00#0#0#8p=7%20#2#2p={%20#2p>0G%20#2#2#2p=c%20#2#2#2#2#2#2#2p>00%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=h%80#=p=Gg00UkR1f1R2<0>0p=fg00VWS00g00W7S01P2P0H04p>0Ag00WiR3?320p=xg00Y6R4f2R5P2P0Ckp=K%00#0#0#1#0#0#1#1#1#0#0#0#0p=^%00#0#0#1p=5%00#0#0#0p=9%00#0#1#0p=F%10#0#0#8p=~%00#0p=H%=0:0>12p=\%10#1p>0F%10#0#1#1p=_%10#0#0#0p=<%10#0#0#1p=L%00#Ap>0<%00#0#0p=B%00#0#8#=p=e%00#1#0#0p=@%00#1#1#1p=:%10#1#1#1#1#1#1#1p=vB0;120p=u%00#1#1#0p=Pg00YTR6%D2;30p>0C%D5%D2=360536p=If3R7%D2=3609365536p=yf4R8A362093659367536p=Z%D7A36209365536p>0B1N75?i20p=S%05#0#0#A,N7?i20p=g%05#A,N7?i20p=}%10#1#0#0p=6%00#1p>0R%00#1#1#1#0#0#0#0p>0[%10#1#0#1p=Y%00#0#1#1p=O%10#8p=s%=09i52p>0Q%10#1#1p>0P%00#1#0#0#0p=X%00#0#0#0#0#0#0#0p=M%00#0#1#0#0#1#1#1p>0O%A0,N2p>0Y%10#0p>0L%82/R0p>0K%00#0#0#1#0#0#1p=]%00#0#1p=n%00#1#0p=mg00Z]R9A3920735p=l%05#8%02#0#0#8'R=390p=b1N87?i52=390p=C%05#8/R2=390p>0J1R52=390p>0V%02#8,R5=390p>0I1R871R52=390539p>0U%08#8/R7%05#8/R2=390539p>0=A3920939593979398p=E%A7,N8?i52=390p=4%17#0#0#0#A,N8?i52=390p=Q%07#A,N8?i52=390p=WP4P4P2P0Ckp=jP5P4P2P0Ckp=pP7P6P6P6P5P2CkP0Ckp=[P5P6P2P0Ckp=|A3920p>0Tf6R:f5R;P8P7P5P2P0H0DH0Dp=zP8P71V52P0H0Dp=dg00[hR<?a20p=rB0\<20p=oA>:;8A>752/?0'?p=U&0]3R0,w4R7g00]6R5#;#J#T$0:#7R2g00][S02%A5#=S03g00^GR;#2R:#2R8#2R=#2R>#2S04#{R?$0G#c$00#hR@#{$00#h#h#h#hRA#DRB40S%15RC#1RD#1RE#1RF#1RG#GRH'f%85S05#=RI+0A&0@3R3'x5K0RJ;>Jg00^fRK$0XRL%^5#5#7RM%05RN#8RO%05#9#5#F#5#~RP%D;RQ%0NRR#0RS#1RT#1RU#0S06#HS07#0RV#ARW'\RX1fQB%0SRY#1RZ#1R[#1R\$0F#A#=R]'fS08PX%1NRN#0R^#0R_#0S09#0R`#GRa%_5#<#L$0:#GRbPI&0<VRV,\QRc&0GA#c#h#h#hS0:#2#cS0;#2S0<#2S0=#cS0>#2S0?#2S0@#2S0A#2S0B#2S0C#2S0D#{$00S0E#2S0F#2S0G#2S0H#2RA%=PS0IPc%0ZRZ#HS0J#HRd#0Re#B#eS0K%05#@#:#T#@#7Rf#=S0L%2A#cRg%2gRg%2gRg%1RRR#0Rh#1Ri#GS0M%1GRj#1#vRk#1Rl#1#;Rm#1#vRn#GRoPI%cgRg#D%2gRg%2gRg%2gRg%2gRg%2gRg%2gRgg00_oRpg00`[Rq#=Rr1uBrRs'uS0N%GTS0O'uRt80;oS0PPt%=MRu%_5#<#L#P#GS0QPIPbPr1usrS0RPIPs%{g$00Rg%2gRg%2gRg%2gS0S&0@6Rg+0C3ICyDZDZ3I3I3IDZ3ICyH0BPr%^5$0:#7S0TP?%BES0U#0S0V$0<,\QS0WCSS0XPr%^5#P#7P?PXCSS0YPr%^5#<#7S0ZP?PXCSS0[PQ%0TRT#1RE#1S0\P?PrCgS0]PQ%0TRT#0S0^#0S0_#0RvP?Q0NC}S0`PQ%BEREP?PBC}S0aPQPVP?%1e#T#GCSS0bPQ%1TRTP?PrCgS0c%8l9tBqS0dPQ%BGP?%D8RGC}S0ePQ%0hRh#0S0f#0S0g#0S0h#0S0i#ARlP?%1^Re#0RV#HRw#AS0j,\QCSS0kPQ%AvP:%0YRv#GRxCSRyPQ%AEP?%0CRC#1RE#1Rz#1#H#6R{#1$0R$0[#P#;#F#9#:#@#P#;#P#J#GCSR|1NQWS0l%H{#_#5#L#9#5#Y#O#@#_#P#O#5#s80Q?R{PQP\P?&0PnRn#H#6#6#6#6#6#6#Y#GCgS0mPQ%B[P?%1n#;#vRn#0#v#v#GC}S0nPQPjP?%0CRC#1Rj#1#O#O#O#O#O#eCgS0oPQ%1vR[#BP?%BiR\#<#L#GC}S0pPQ%1e#9P?Q00P8PqP?H0ZRePQ%0vRv#HS0q#HRW#AP?%X5#:#;#F#7R}#=R~CSS0rPQ%1vP?PrCgS0sPQ%1[P?1\QlRlCgS0tPQ%1ZP?Q0WCgS0WPQ%AdP?%1RRR#1Rd#BRZ#AS0u,\QCSR[PQ%1VP?PrCgPQ%HwP?PrPQ%1_R_P?PrPQ%9_P?PrPQQ09P?PrPQ%0`R_#HP?PrPQPdP?%GNRdPQPZP?&0R5#5#5#M#eS09PQ%0RRRP?PIPQ%HRRR#0RZP?P~PQPiP?%_5#<#<#F#GPQP\P?PuPQ%1hS0v#BS0wP?%H5#9#5#6#:#ePr%^5#O#7P?PrPr%^5#F#7RhP?PrPr%05$0O#5#F#7RiP>%1n#;Rn$0P#v#sRw#=Pr%^5#Y#7P?PaPr%^5#6#7RVP?PXPrPMP>PdPQQ0hP?PrPQP\P?PrPQPZP?PrPQQ0uP?PrPQQ07P?PrPQ%1US07#BS0uP?%1NRN#BRU$0<RZ,\QR\PQQ0_P?PePQQ0JP?PrPQQ0qP?PrPQ%BFP?1fQxRxPQQ0VP?PGPQ%0DRDP?%=ORFPQ%HDRD#0RdP?P~PQ%BzP?%15#;#Y#6#Y#ePQ%BEREP?P\PQ%BjP?PePQPRP?PrPQP_P?PrPQQ0jP?%D@R@PQPZP?PGPQQ0^P?%GDPQQ0gP?PrPQ%0CRC#HRZP?PFPQPNP?%<5#_#P#9#ePr%05#@#:#<#;#~P>1u@r:0;pr%9k#M#M#M#7Rk%HWRW#9Rp#B#9RN#0RR#<#M#M#7Re5tG%Bn#M#s=t@wPQQ0UP?PrPQPdP?PrPQPEP?PrPQPZP?PrPQPUP?PxPQP`P?%<5#T#6#:#ePQQ0fP?PFPQPvP?%8SRS#=Rv,fQPQPDP?%15#J#P#L#;#e%8YRY-0?Q%9R#M#M#79tQk20YQNRR%8NRN+0NPQPqP?PFCSPQPSP?%D:PQPYP?PGPQ%8CP?Pr%D=R=?tke%D>RC?tkePRPN1N=q%8_H0MPRPN1NCqPYH0M20?=S20?CS&0LT#M#7,Nr&0L5#@#M#7+0N20KpM%]5#6#9#PPh%]5#6#5#9Q0T%]5#6#5#6Q0Z%]5#6#F#@PV%]5#6#O#<Pi%]5#6#@#T%05$0O#@#F#7%]5#Y#9#<#s%]5#Y#F#6#sRiPi%n5#5#Y#F#6#sRi%n5#5#J#F#<%n5#5#J#L#6%X5#:#T#LPr%05#@#:#<#_#7RVP?%=VPr%05#@#:#<#;#7P>Q04#DRV%n5#5#J#@#F%05#@#:#L#T%n5#5#J#P#6%05#@#:#L#J%n5#5#J#:#6%05#@#:#T#F%n5#5#J#L#<%m5#5#J#_#91Nr}@0Wv8%@5#O#;#L#<%X5#:#;#@#7+0K%m5#5#;#Y#<#s%X5#:#;#:#7RvPrPvP?P=%m5#5#;#J#9%X5#:#;#L%m5#5#;#J#6%X5#:#;#6#7R=PrP=P?%8WRW#=%m5#5#v#@%X5#<#9#O%m5#F#9#5#9%X5#<#:#T%m5#F#5#;#9%X5#T#MQ05%8m5tV1RqW&0@93l3b3b3bDC40J3bDC40V3l80J}60If3b3b3bDCDC3b60IiI0UI0=I0=I0=DEDEDCDCDCDED4D4D4D4D4D4D4D4D43lDCDQDWD4D4DCDCD4D4D4DWD4DWDQD4D4D4D4D4D4D4DCD4D4D4DCDCDCDCDCDCRiD4DWDQDWDQDWDQD4DQD4DQD43lDED43lDEDEDEDERfN<05,`KR};>}R91w44RW/w4R41jPM=pWORP;>PRq1w66RV/w6Rm/w6R=PVPXQ08PbC[=|mIRv;>vR8AK023Rh=>7hRpPMPO%05#M#J#:#~RTPXPXPXPaPrPrPlQ0S#2RC%=TPlQ0KQ0L%2C#cRS%2SRS%2SRSPu1uItPr%cSRS#D%2SRS%2SRS%2SRS%2SRS%2SRS%2SRSP~PIQ09PrPrPrPrPrPrPr%{S$00RS%2SRS%2SRS%2S00Cg3ICyDZDZ3I3I3IDZ3ICyH0BRSQ0XQ0YQ0[Q0]Q0`Q0aQ0bQ0cQ0dQ0eQ0kPyQ0mQ0nQ0oQ0pQ0rQ0sQ0tQ0W20T[iDEDERi9l|{DEDEDEN<05,`KR{=>L{R[1jTM=pWOR~=>4~RYPVPXPXPrC[RN=>mNRR%;5#@#9#:#~=K03R_=>7_Re20AHBg00a9Rkg00aYRFPkP;P>PBH0HQ0RH04/x3'x9K02RD=>7DR`PMPO%05#9#F#P$0:#~RxPX1fQ]RUPXPaPGPBPcQ0:%=xPcQ0KQ0LQ0;Q0<Q0=Q0MPoPBQ0>#DQ0?Q0@Q0AQ0BQ0CQ0DPrQ0OPuPbPrPGPrQ0RQ0NPsQ0EQ0FQ0GQ0H00Cg3ICyDZDZ3I3I3IDZ3ICyH0BPfN<05,`KRf=>LfRg1jxM=pWORx=>4xRsPVPXPUPGC[RG=|mBRB=>=BRU%05#5#O#L#P#7=K03R5=>75RcPMPOPTPXQ0\$0F#A,\QRTPXPaPrPrPlPSQ0XQ0YQ0[Q0l%8^80Q:PQQ0vP?Q0QPQQ0wP?PuPQQ0fP?PtPQQ0iP?Q0PPQQ07P?PoPQQ0uP?Q0MPQQ06P?Q0IQ0]Q0`Q0aQ0bQ0cQ0dQ0eQ0kAly|iDEDEDQDWDQDWDQDWDQDEN<05,`KRi=>LiR|PVPXPTPrC[RT=>mTRy/?eR?,?YRo'?Rt,?pRu'?R:'?R^'?RS'?Rl'?Ra'?RO'?RM'?RZ'?RE'?Rd'?R@'?Rw'?P7PJP9PwPLP}PqP@P4PPP8PdP=PvPpPE1V7hREP[PZ1VL{PYPM1V4~RMPRPO1VmNPePa1V7_RaP`Pl1V7DPgPSPLPfPsP^P4PxPUP:P=PBPcPuP7P5PpPtPEP|Po1VLiPYP?PMPyPe1VmTPaFzFzDdDdDdDdFzFzFzDdDdDdDdP71w<0R<g00bKRag00cW3aRe,r0#q1o0e5K0Q02Q03g00dTRe40S/fH00AI/x39K02PLg00ePRyg00fKRMPAg00gHg00hFI03g00iDRA,`KP4&06A&02A'j&08A5pWPPP=PV&09A&01A&0EAC[&07A5|mPVPXB0>1Qe/f]PbC[=|mIP7g00jB9a<aRI,r0#q1o0I5K0PhPLPyPMPCg00k?g00l=I03g00m;RI,`KP4&06I&02I'j&08I5pWP~PmPV&09I&01I&07IC[PNP7g00n99a<aRN,r0#q1o0N5K0P_P7g00o69a<aRN,r0#q1o0N5K0Q00Q01PHPeH04PkPFPkP;P>PeH0HB0;1er/urH04/x3'x9K02PLPyPMQ0:g0103g0111I03g011oR2,`KP4&062&022'j&0825pWPxP=PV&092&012&0E2C[&0725|mPmP6PGPeCkP7g012m9a<aRe,r0#q1o0e5K0P5P7g013j9a<aR5,r0#q1o055K0PhPLPyPMPCg014gg015eI03g016cRC,`KP4&06C&02C'j&08C5pWP~PmPV&09C&01C&07CC[PTg017a9a<aRa,r0#q1o0a5K0=>7_FUFUFUFUFUFUFUFUFUdo"). Qed.
End VP1.

Section VP2.
Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x10ab4c%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x109cb0%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x109cb0%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x10a784%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x109cb0%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x109cb0%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x109cb0%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xff528%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x10073c%Z, 0x113808%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xfa03c%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O23OpenFail_defs ()) ["VP2"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10TTg000Pj2kTg007gj10Tg006Kj1uTg006kj3ATg002Wj12Tg0036j1LTg001Nj18Tg005Hj11Tg00E^j4cTg00:`j2HTg018^k404Tg00DUj4{Tg0010j1WTg004?k30>Tg005mj17Tg007Ek10STg008Lj3pTg009Uj3fTg00;jk40QTg00=3j2wTg00>>k207Tg00?Ik406Tg00@Tk30OTg00A_j2TTg00Bjm<0LTg00D3j2~Tg00Rhj4RTg00Fkj2FTg00GFj2}Tg00G`j3NTg00Q_j3sTg00IDk50ITg00JLk10HTg00KPk10GTg00LRk10FTg00MUk10DTg00NXk10CTg00P]k10BTg00SHj3<Tg00Shj3hTg00U3k40?Tg00H=j1|Tg00UNk308Tf0R0#0#0#0#1p=6%00#1#0#1p=z%00#1#1#0p=B%10#0#0#1p=J%10#0#0#7p=ng00Y6R1f2R2f1R3P0CRp=M%00#0#1#1p=D%00#0#0#7p=5%20#2p=o%20#2#2#2p=r%20#2#2#2#2#2#2#2p=x%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>0=g00UkR4?p30p=e%10#1#1#1#1#1#1#1p=b%10#1#1#1p=:%10#1#1p>02%00#0#0p=?%00#0#0#0#0#0#0#0p=I%10#7p=gg00WiR5?<30p=P%00#1#0#0p=>%00#0#0#0p=;%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=lAs430p=E%70#8p=Vg00a9R6g00W7S00P3P0Ccp=y%10#1#1#0p=G%10#0#1#0p=Q%00#0#0#1#0#0#1#1#1#0#0#0#0p=a%00#1#1#1p==%00#0p=K%00#Wp=j%00#0#7#8p=_%00#1#0#0#0p=Z%00#0#1#0p=C%00#1p>0<g00YTR7%L2%L3=<703<p=iA<7309<72p=Y%L3=<70p>0;%10#0#0#0p=@%10#0#1#1p=qf3R8/H2?h30p>0:%10#1#0#0p=4%00#1#1#1#0#0#0#0p>0R%00#0#1p=[%10#1#0#1p=^%00#0#1#0#0#1#1#1p>09%W0,H3p>0P%10#0p>05%73/T0p>03%00#0#0#1#0#0#1p=`%00#1#0p=dg00Z]R9A<9307<2p=S%02#7%03#0#0#7'T=<90p=]f4R:/H8?h23=<90p=9%02#7/T3=<90p>011T23=<90p>0N%03#7,T2=<90p>001T:81T23=<905<9p>0M%0:#7/T8%02#7/T3=<905<9p=v%W8,H:?h23=<90p=3%18#0#0#0#W,H:?h23=<90p=U%08#W,H:?h23=<90p=X%W8,H:%73#87h2=<90p=mP7P7P3P0CRp=tP:P81}23P0H0?p=Og00[hR;?N30#|p>0EB08;30p>0AP1P8P2P3CR=A:0p>0JAA823/F0p>0Kf6R<f5R=;A:AA823/F0'Fp>0@f7P1P<AN;=:#|B08;82CR;A3/F0p=\&0T5R0,k1R3g00]6R8#0#6#z#B#J#n%u5R55M0R2;A2%08#6#D#J#B#5R=g00VWR:g019kg00^GR<#2R>#2R?#2R@#2RA#2RB#2#oRC#o#r#x$0=RD#LREg00`[RF#8RG'eRH%18RI#1RJ#1RK#1RL#1RM#1RN#1#bRO#1RP#1#:RQ#1#bRR$02RS#1#:#bRT#1#:RU#?#I#gRV#8Cc/P55M0RW=A3WS01AM0=5RX=A3XS02%08#6#>#:#;#n=M05RY=A3YS03P:g01:]S04%2D#o#x#l#lRD#LRZ/eGR[PZCc%L?R\/EZ/HFP>P:PGH04/P5'P9M0=R]=A3]S05%VMR^/yZP6g00aYS06P6P<PAPZC{1e[GCc/P5'P9M0=R_=A3_S07g00][S08%W8#8S09<0>Z/E^%78R`#8Ra'y/P59M0=Rb=A3bS0:%:8#G#Q#z#5=M05Rc=A3cS0;g00^fRd$0SS0<%a8#6#5Re%08Rf#7Rg%08#I#G#=#nRh%L<Ri%0fRj#0Rk#1Rl#1Rm#0S0=#KS0>#0S0?#WS0@#8'ERn1EiZ%0kRo#1Rp#1Rq#1Rr#1#j#8Rs'ERtPn%1fRf#0Ru#?Rv#VS0APGPG%1jRj#0Rw#0Rx#0Ry#0S0B#0S0C#0S0D#WS0E#8,EiRz%oD#r$0=#l#l#lRD%8h%0pS0F#KS0G#KS0H#0Rp#?#_%08#>#=#Q#>#5R{#8%2D#rR|%2|R|%2|R|%8eS0I1eG[S0J%Vl'eR[,ea%r|R|#L%2|R|%2|R|%2|R|%2|R|%2|R|%2|R|%Z8#=#:#C#5R}#8R~&0<8#6#6#I#_%2|#o#xR|%2|R|%2|R|%2|%u73i3i9YGG9YGG9YGG7YG7Ya3i3i3i5YG3Y+0;3i3Y7Yz+0;PG%a8#z#5S0KPC%?KS0L#0S0M#j#8,EiRKPG%a8#B#5PCPnPG%a8#@#5S0NPCPnPi%1xRxPC%q8#@#J#B#VPi%;xPCQ0IPiPyPCP[PiQ0DPCg00_oRx%VRRR;p[Pi%1mRmPCPRPi%?mRmPC%1wRw#VPiQ0=PC%K8#;#C#>#D#_Pi%0lRl#1RRPCPGPi%0lRl#0S0=#0R[#0R|PCQ0JPi%?RRRPCPZPiQ0?PC%1p#Q#VPi%1lRl#?PCPG%7P9fZFPi%?M#jPCP\H0:PiQ0EPC%1u#K#jRu#8,EiPiP|P>%0oR|#VRMPiPRPC%0IRI#1RR#1RZ#1#K#4RP#1$0<$0R#B#:#C#;#=#>#B#:#B#GPiQ0@PC%[P#B#D#C#;#D#Q#B#J#B#4#B#D#VPi%?rPC%KS#4#4#4#4#4#4#^Pi%;qPC%0T#b#bPi%?NPC%0IRI#1RN#1#D#D#D#D#D#_Pi%1|RT#;PC%?wRw#@#JPi%0|R|#KRq#KRSPCP~PiP|PCPGPiPTPCPzPiQ0FPCPKPiQ0HPC%1jRj#1#K#jRK#8,EiPG%a8#D#5PCPGPG%a8#C#5RzPCPGPG%08$09#6#C#5RTPA&02U#b#gRU#8PG%a8#^#5PCQ0APG%a8#4#5RrPCPnPGPePA%VfPiQ0CPCPGPiPwPCPGPi%?jRjPCPGPiPKPCPGPiQ0>PCPGPiPmPC%1fRf#?Rm#jRK#8,EiRwPiP[PCP:P?PFPCH0QR[PiQ0GPCPGPiPqPCPGPi%?LPC1EiMRMPiQ0MPCP\Pi%0JRJPC%8gRLPi%KJRJ#0RqPCP~Pi%?ZPC%18#:#^#4#^#_Pi%?RRRPCPwPi%?NPCP[PiPjPCPGPi%0vRjPCPGPiPuPCPEPiPKPCP\PiQ0=PCPJPiQ0BPCPGPi%0IRI#KRKPCPLPiPfPC%@8#q#B#;#_PG%08#>#=#@#:#nPAApxGH%;O#I#I#I#5RO%KSRS#;Rx#?#;RH#0Rf#@#I#I#5Ru5f\AfEVUPiQ0LPCPGPiPqPCPGPiPRPCPGPiPKPCPGPiPmPCPMPiPvPC%@8#Q#4#=#_PiPyPCPLPiP|PC%7kRk#8R|,EiPiPJPC%18#G#B#J#:#_%7oRo,wi%;f#I#I#59fiO20PiHRf%7HRH+07PiPFPCPLH0:PiPkPC%L>PiPoPCP\Pi%7IPCPG%L@R@?fOu%LARI?fOuPfPH1H@F%7jH06PfPH1HIFPoH061w@k1wIk&05l#I#5,HG&058#>#I#5+07203xe%`8#4#;#BPz%`8#4#6#;Q0K%`8#4#6#4Q0N%`8#4#C#>Pr%`8#4#D#@PT%`8#4#>#Q%08$09#>#C#5%`8#^#;#@#g%`8#^#C#4#gRTPT%[8#6#^#C#4#gRT%[8#6#G#C#@%[8#6#G#J#4%Z8#=#Q#JPG%08#>#=#@#q#5RrPC%8rPG%08#>#=#@#:#5PA%LBRB%[8#6#G#>#C%08#>#=#J#Q%[8#6#G#B#4%08#>#=#J#G%[8#6#G#=#4%08#>#=#Q#C%[8#6#G#J#@%d8#6#G#q#;1HG}@0O|?%>8#D#:#J#@%Z8#=#:#>#5+03%d8#6#:#^#@#g%Z8#=#:#=#5R|PGP|PCP@%d8#6#:#G#;%Z8#=#:#J%d8#6#:#G#4%Z8#=#:#4#5R@PGP@PC%7SRS#8%d8#6#b#>%Z8#@#;#D%d8#C#;#6#;%Z8#@#=#Q%d8#C#6#:#;%Z8#Q#I%7Q9fB`1TFS%u93S3]3]3]D94013]D940N3S801}600{3]3]3]D9D93]600TI0MDvDvDv3S3S3S3SD9D9D93S3SD3D3D3D3D3D3D3D3D33SD9DUDXD3DmD9D9D3D3D3DXD3DXDUD3D3D3D3D3D3D3D9DXD3D3D9D9D9D9D9D9D3DUDUDUD3DmD3DmDmD9DmD3D93SD3DXDXDXDUDUDXDUDXDUD3DUD9D9D9N<0L,~dRT;ATR{1k11R}/k1R9P}P1P1P1PhPeCRPgCRRg;AgRe1k77Rh/k7RSPhP71tntPGCRRt;AtRB%:8#>#;#=#n=M05R8=A38R`'FRQ'FRC'FR@'FR|'FR?'FRr'FRz'FRx'FRl'FP3P2Q01PlP3PWQ02PxP3PXQ03PzP3PYQ05PrP3P]Q07P?P3P_Q0:P|P3PbQ0;P@P3PcP{PCQ0<PTPePQP9PgPBP`PSPt1}38DODODODODODODODODODODOP3P0P01k;0R;g00bKRtg01;O3NR`P0P`P2P3P0P0g01<K9N;tR2P0P2PWP3P0P0g01=G9N;tRWP0PWPXP3P0P0g01>C9N;tRXP0PXPYP3P0P0g01??9N;tRYP0PYP:Q04g00dTRY=p4GRXPYCcAs4\Y/HFP>P:PGH04/P5'P9M0=P3P0P0g01@;9N;tR:P0P:P6Q00P^PYCcP6Q06P6P<PAPYC{1eXGCc/P5'P9M0=P3P0P0g01A79N;tRXP0PXQ08Q09<0>Y/E^/ya/P59M0=P3P0P0g01B39N;tR=P0P=PcQ0<g00ePg00fKPDg01Bog01ClI0Ig01DiRD,~dP9P}P1P1P1&0HD&0GDCR&0FDCRPgPSPhP7&0DD&0CD't&0BDCRPhP7As4iY/Es,tnPGCRP3P0g01Eg9N;tRt-0E020A0tP8I0JH0KK0@G\G\G\G\G\G\G\G\do"). Qed.
End VP2.
