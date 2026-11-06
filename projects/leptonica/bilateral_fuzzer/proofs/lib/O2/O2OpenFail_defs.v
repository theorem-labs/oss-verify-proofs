(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MainEntry O2LibStdioCall.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2PXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2RelocImg7o2_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4srG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4knG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4scG3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4srH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4knH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4scH3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rI3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4srF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4knF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4scF4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rG4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4srH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4knH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4scH4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3rI4C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond06C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib2O2?O2OpenFail_defs2rAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rDC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3srHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs3knHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs4scOFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2?O2OpenFail_defs2rIC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x36a58; 0x36e5c; 0x36fe4; 0x3698c; 0x12ac0; 0x12c4c; 0x30ef0; 0x2f4d4; 0x31958]%Z.
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
Definition IHI : Z := 0x6b000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x17618 sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x37344 srB0 [] knB0 39.
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
Definition ssC0 : sym_state := SS 0x31d38 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x31d38 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x326c8 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x31d38 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x31d38 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x31d38 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x32028 srI0 [] knI0 263.
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
Definition ssI30 : sym_state := SS 0x32028 srI30 [] knI30 263.
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
Definition ssH40 : sym_state := SS 0x31d38 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x32028 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Section VP1.
Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0x31958%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x321f8%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x11cf6, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x31958%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x2f4d4%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0x31958%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x32c18%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x31958%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x2f4d4%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10[Tg000Pj2tTg0010j1?Tg001Nj1;Tg002Wj12Tg0036j1@Tg004?k30QTg005Hj11Tg005mj18Tg006Kk10BTg006kj39Tg007Ek10UTg007gj10Tg008Lk30:Tg009Uj3pTg00:`j2OTg00;jk40XTg00=3k20ATg00>>k20LTg00?Ik40KTg00@Tk30VTg00A_j2VTg00Bjm<03Tg00D3j2\Tg00DUk40ITg00E^k402Tg00Fkj2:Tg00GFj2ZTg00G`j3[Tg00H=j1mTg00IDk504Tg00JLk107Tg00KPk105Tg00LRk106Tg00MUk101Tg00NXk109Tg00O[k10GTg00P]k108Tg00Q_k30;Tg00Rhj4lTg00SHj35Tg00Shj3oTg00U3k40FTg00UNk30ZTf0R0#1#0p=a%00#0#1#1p=A%00#0#1#0p=M%10#0#1#1p=>%00#0#0#8p=3%20#2#2p=|%20#2p>0H%20#2#2#2p=g%20#2#2#2#2#2#2#2p>00%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=f%80#;p=Bg00UkR1f1R2<0;0p=cg00VWS00g00W7S01P2P0H02p>0Cg00WiR3?520p=wg00Y6R4f2R5P2P0Clp=J%10#1#0#0#1#0#1#0#1#0p=_%00#0#0#1p=~%00#1#0#0p=F%10#1#1#1p=L%00#0p=<%;0:0;12p=e%10#1p>0>%10#1#1p>0=%00#?p>0<%00#0#0#0p=7%00#0#8#;p=]%00#0#1p=u%10#0#0#0p=H%10#1#1#1#1#1#1#1p=zB0:120p=sg00YTR6%@2;50p>0E%@5%@2=560556p=Ef3R7%@2=5609565556p=yf4R8A562095659567556p=Y%@7A56209565556p>0D%00#1#0#1p=S%00#0#0p=G1O75?o20p=R%00#1#1#0p=I%05#?,O7?o20p=N%00#1#1#1p=d%10#0#1#0p=K%10#0#0p=q%10#1#0#0p=4%10#0#1p>0Y%10#1#1#0p=x%10#0#0#1p=W%10#1#0#1p=C%10#8p=n%;09o52p>0P%10#0#1#0#0#1#1p=b%10#1#0#0#1#0p>0O%00#1p>0N%00#0#1#0#0p=`%00#8p>0M%00#0#0#0#0#0#0#0p=P%?0,O2p>0W%82/V0p>0Jg00Z]R9A5920755p=k%02#8,V5=590p>0@%08#8/V7%05#8/V2=590559p=v1O87?o52=590p==1V52=590p>0T%05#8/V2=590p>0?1V871V52=590559p>0SA5920959595979598p=D%?7,O8?o52=590p=6%17#0#0#0#?,O8?o52=590p=Q%07#?,O8?o52=590p=UP4P4P2P0Clp=jP5P4P2P0Clp=hP7P6P6P6P5P2ClP0Clp=XP5P6P2P0Clp=}A5920p>0Rf6R:f5R;P8P7P5P2P0H0FH0Fp={P8P71Z52P0H0Fp=^g00[hR<?[20p=iB0Z<20p=rA9:;8A9752/:0':p=T&0[3R0,t4R7g00]6R5#a#A#M#>#3R2g00][S02%?5#;S03g00^GR;#2R:#2R8#2R=#2R>#2S04#|R?$0H#g$00#fR@#|$00#f#f#f#fRA#@RB40Q%15RC#1RD#1RE#1RF#1RG#BRH'c%85S05#;RI+0C&0B3R3'w5J0RJ;9Jg00^fRK$0URL%_5#~#3RM%05RN#8RO%a5#F#A#L#3RP%@;RQ%0NRR#0RS#1RT#1RU#0S06#<S07#0RV#?RW'eRX1cQB%0SRY#1RZ#1R[#1R\$0>#?#;R]'cS08PX%1NRN#0R^#0R_#0S09#0R`#BRa%1US0:#<RU$0=Rb#>Rc#0#BRdPI&0<VRV,eQRe&0HA#g#f#f#fS0;#2#gS0<#2S0=#2S0>#gS0?#2S0@#2S0A#2S0B#2S0C#2S0D#2S0E#|$00S0F#2S0G#2S0H#2S0I#2RA%;PS0JPe%0ZRZ#<S0K#<Rf#7#]S0L%u5#A#7#H#3S0M#;S0N%2A#gRg%2gRg%2gRg%1RRR#0Rh#1Ri#BS0O%1GRj#1#zRk#1Rl#1#LRm#1#zRn#BRoPI%ggRg#@%2gRg%2gRg%2gRg%2gRg%2gRg%2gRgg00_oRpg00`[Rq#;Rr1sBrRs'sS0P%BTS0Q'sRt80:oS0RPt%;MRu%1c#BS0SPIPdPr1ssrS0TPIPs%|g$00Rg%2gRg%2gRg%2gS0U&0B6Rg+0E3ECyDYDY3E3E3EDY3ECyH0DPr%_5#S#3S0VP?%GES0W#0S0X$0<,eQS0YCRS0ZPr%_5#I#3P?PXCRS0[Pr%_5#H#3S0\P?PXCRS0]PQ%0TRT#1RE#1S0^#<P?PrCNS0_PQ%0TRT#0S0`#0S0a#0RcP?Q0PCNS0bPQ%GEREP?PBCNS0cPQPVP?%0YRV#0Rv#1Rw#1#d#K#BCRS0dPQ%qTP?PrCNS0e%8l9pBqS0fPQ%GGP?%@8RGCNS0gPQ%0hRh#0S0h#0S0i#0S0j#0S0k#?RlP?%1^RT#0Rx#<Ry#?S0l,eQCRS0mPQ%?cP:%BVRcCRRzPQ%?EP?%0CRC#1RE#1R{#q#4R|$0Y#d#7#I#L#M#7#d#F#I#L#I#x#BCRR}1OQWS0n%<|#>#~#W#7#~#C#A#F#>#I#A#~#n80P?R|PQ%<\P?&0=nRn#<#4#4#4#4#4#4#C#BCNS0oPQ%G[P?%1n#L#zRn#0#z#z#BCNS0pPQ%<jP?%0CRC#1Rj#1#A#A#A#A#A#]CNS0qPQ%1VRV#GP?%GiR[#H#W#BCNS0rPQ%1T#7P?Q00P8PqP?H0XRTPQ%<vS0s#<R\#?P?%b5#S#S#3RW#;R~CRS0tPQ%<wP?PrCNS0uPQ%qVP?1eQlRlCNS0vPQ%qZP?Q0YCNS0YPQ%?fP?%1RRR#1Rf#GRZ#?RV,eQCRRwPQ%qxP?PrCNPQ%<yP?PrPQ%1_R_P?PrPQ%7_P?PrPQQ09P?PrPQ%0`R_#<P?PrPQPfP?%BNRfPQPZP?%K5#d#4#M#]RZPQ%0RRRP?PIPQ%<RRR#0RyP?P~PQPiP?%0b#A#BPQP[P?PuPQ%1hS09#GS0wP?%q5#H#7#M#]Pr%_5#A#3P?PrPr%_5#M#3RhP?PrPr&0O5#>#M#3RbP>%1n#LRn$0=#z#nRi#;Pr%_5#C#3P?PaPr%_5#4#3RxP?PXPrPMP>PfPQQ0jP?PrPQP[P?PrPQPyP?PrPQPVP?PrPQQ07P?PrPQ%0US07P?%1NRN#GRU$0<RV,eQRyPQQ0aP?PTPQQ0KP?PrPQQ0sP?PrPQ%GFP?1cQcRcPQQ0XP?PGPQ%0DRDP?%;ORFPQ%0DRD#0R[#0RfP?P~PQ%G{P?%q5#I#C#W#]PQ%GEREP?PyPQ%GjP?PTPQPRP?PrPQP_P?PrPQQ0lP?%@@R@PQPVP?PGPQQ0`P?%B[PQQ0iP?PrPQ%0CRC#<RVP?PFPQPNP?&0N5#x#~#L#]Pr%`5#>#4#x$0MP>1s@r:0:pr%7k#P#P#P#3Rk%<\R\#7Rp#G#7RN#0RR#H#P#P#3RT5pG%Gn#P#n=p@iPQQ0WP?PrPQPfP?PrPQPEP?PrPQPVP?PrPQPUP?PcPQP`P?&0N5#C#H#I#]PQQ0hP?PFPQPvP?%8SRS#;Rv,cQPQP[P?%05$0>#>#L#I#]%8YRY-0AQ%7R#P#P#39pQk20WQNRR%8NRN+0LPQPqP?PFCRPQPSP?%@:PQPYP?PGPQ%8CP?Pr%@=R=?pkT%@>RC?pkTPRPN1O=q%8_H0KPRPN1OCqPYH0K20A=S20ACS%aD#P#3,Or%a5#F#P#3+0L20JpM%45#K#H#IPh%45#K#W#7Q0V%45#K#W#4Q0\%45#K#K#FPx%45#K#>#HPb%45#K#4#K&0O5#C#x#3%45#>#d#H#n%45#>#W#4#nRbPb%`5#>#W#4#nRb%`5#>#>#H%`5#4#M#4%b5#7#C#3Pr%u5#M#x#L#3RxP?%;xPr%u5#M#L#A#3P>Q04#@Rx%`5#>#C#M%u5#M#L#x#3%`5#>#L#4%u5#A#7#M#3%`5#4#7#4%u5#A#7#I#3Q0M%`5#4#M#H%15#F#4#F#71OrW@0Vv8%a5#W#K#>#7%b5#S#d#3+0J%15#F#C#I#F#n%b5#S#K#3RvPrPvP?P=%15#F#C#I#4%b5#S#4#3%15#F#C#d#H%b5#S#L#3R=PrP=P?%8\R\#;%15#F#C#H#7%b5#I#I#3%15#F#C#W#4%b5#C#C#3R=%15#S#H#PQ05%8m5px1Vq\&0B93k60@=DvD=DvD=40T3k80?W40@40?DvD=D=40?60@bI0SDvDvDvDDDDD=D=D=DDD6D6D6D6D6D6D6D6D63kD=DQDUD6D6D=D=D6D6D6DUD6DUDQD6D6D6D6D6D6D6D=D6D6D6D=D=D=D=D=D=RbD6DUDQDUDQDUDQD6DQD6DQD63kDDD63kDDDDDDDDRWN<03,\KR=;9=R91t44R\/t4R41jPM=h\ORP;9PRq1t66Rx/t6Rm/t6RvPxPXQ08PdCX=}mIR8;98RhAJ023Rp=97pRDPMPO%a5#F#7#S#3RCPXPXPXPaPrPrPlQ0U#2RS%;CPlQ0LQ0N%2S#gRY%2YRY%2YRYPu1sItPr%gYRY#@%2YRY%2YRY%2YRY%2YRY%2YRY%2YRYP~PIPZPrPrPrPrPrPrPr%|Y$00RY%2YRY%2YRY%2Y00Eg3ECyDYDY3E3E3EDY3ECyH0DRYQ0ZQ0[Q0]Q0_Q0bQ0cQ0dQ0eQ0fQ0gQ0mPzQ0oQ0pQ0qQ0rQ0tQ0uQ0vQ0Y20RwbDDDDRb9k}|DDDDDDN<03,\KR|=9L|Rw1jCM=h\ORZ=94ZR~PxPXPXPrCXRN=9mNRR%d5#K#I#K$0M=J03R_=97_RT20CHBg00a9Rkg00aYRFPkP;P>PBH0IQ0TH02/w3'w9J02R[=97[R`PMPO%a5#S#H#A#3RcPX1cQ]RUPXPaPGPBPeQ0;%;cPeQ0LQ0NQ0<Q0=Q0>Q0OPoPBQ0?#@Q0@Q0AQ0BQ0CQ0DQ0EPrQ0QPuPdPrPGPrQ0TQ0PPsQ0FQ0GQ0HQ0I00Eg3ECyDYDY3E3E3EDY3ECyH0DPWN<03,\KRW=9LWRg1jcM=h\ORc=94cRsPxPXPUPGCXRG=}mBRB=9vBRU%a5#C#F#>#3=J03R5=975RePMPOPCPXQ0^$0>#?,eQRCPXPaPrPrPlPYQ0ZQ0[Q0]Q0n%8^80P:PQQ09P?Q0SPQQ0wP?PuPQQ0hP?PtPQQ0kP?Q0RPQQ0:P?PoPQQ07P?Q0OPQQ06P?Q0JQ0_Q0bQ0cQ0dQ0eQ0fQ0gQ0mAkz}bDDDDDQDUDQDUDQDUDQDDN<03,\KRb=9LbR}PxPXPCPrCXRC=9mCRz/:TR?,:~Ro':Rt,:DRu':R:':R^':RY':Rl':Ra':RO':RM':RV':RE':Rf':R@':Ri':P7PJP9PiPLP=PqP@P4PPPhPfPvP8PDPE1Z7pREPwPV1ZL|P~PM1Z4ZRMPRPO1ZmNPTPa1Z7_RaP`Pl1Z7[PgPYPLPWPsP^P4PcPUP:PvPBPePuP7P5PDPtPEP}Po1ZLbP~P?PMPzPT1ZmCPaF{F{D^D^D^D^F{F{F{D^D^D^D^P71t<0R<g00bKRag00cW3[RT,i0#m1r0T5J0Q02Q03g00dRRT40Q/cH00CI/w39J02PLg00eLRzg00fDRMPAg00g>g00h:I04g00i6RA,\KP4&07A&05A'j&06A5h\PPPvPx&01A&09A&0GACX&08A5}mPxPXB0;1QT/c]PdCX=}mIP7g00j29[<aRI,i0#m1r0I5J0PpPLPzPMPSg00jmg00kiI04g00leRI,\KP4&07I&05I'j&06I5h\PZPmPx&01I&09I&08ICXPNP7g00ma9[<aRN,i0#m1r0N5J0P_P7g00n\9[<aRN,i0#m1r0N5J0Q00Q01PHPTH02PkPFPkP;P>PTH0IB0:1Tr/srH02/w3'w9J02PLPzPMQ0;g00oWg010SI04g011OR2,\KP4&072&052'j&0625h\PcPvPx&012&092&0G2CX&0825}mPmP6PGPTClP7g012K9[<aRT,i0#m1r0T5J0P5P7g013F9[<aR5,i0#m1r055J0PpPLPzPMPSg014Ag015=I04g0169RS,\KP4&07S&05S'j&06S5h\PZPmPx&01S&09S&08SCXPCg01759[<aRa,i0#m1r0a5J0=97_FTFTFTFTFTFTFTFTFTdo"). Qed.
End VP1.

Section VP2.
Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x37340%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x36a58%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x36a58%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x36fe4%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x36a58%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x36a58%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x36a58%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x31958%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x32028%Z, 0x39508%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x2f4d4%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_O2OpenFail_defs ()) ["VP2"] "p%0p&0p;1p;2p;3p;4p;<p;5g0000k10RTg000Pj2lTg006Kj1yTg006kj3<Tg002Wj12Tg0036j1KTg001Nj16Tg005Hj11Tg00E^j4dTg00:`j2ITg0180k40:Tg00DUj4|Tg0010j1ZTg004?k30<Tg005mj18Tg007Ek10QTg007gj10Tg008Lj3pTg009Uj3cTg00;jk40OTg00=3j2zTg00>>k204Tg00?Ik403Tg00@Tk30MTg00A_j2UTg00Bjm<0JTg00D3k201Tg00Rhj4OTg00Fkj2CTg00GFk200Tg00G`j3MTg00Q_j3tTg00IDk50GTg00JLk10FTg00KPk10ETg00LRk10DTg00MUk10ATg00NXk10BTg00P]k10CTg00SHj3:Tg00Shj3hTg00U3k40=Tg00H=j1~Tg00UNj3}Tf0R0#1#0p=a%10#1#1#0p=]%00#1#1#0p=;%10#0#0#0p=?%00#0#0#8p=4g00Y6R1f2R2f1R3P0COp=J%10#1#0#1p=@%00#1#0#0p=H%10#0#1#1p=A%20#2p=o%20#2#2#2p=q%20#2#2#2#2#2#2#2p={%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>09g00UkR4?p30p=b%10#1#1#1#1#1#1#1p=i%10#1#1#1p=E%10#1p=x%00#0#0p==%00#0#0#0#0#0#0#0p=N%10#8p=fg00WiR5?:30p=P%00#1#1#1p=Q%00#0#1#0p=B%00#8p=s%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=mAt430p=D%80#6p=Tg00a9R6g00W7S00P3P0Cdp=r%00#0#1#1p=G%10#1#0#0#1#0#1#0#1#0p=`%00#0#0#1p>0;%00#0#0#0p=9%00#1#0#1p=Y%00#0p=F%00#Zp=k%00#0#8#6p=_%00#0#1p=e%10#0#1#0#0#1#1p=^%10#0#1#0p=>%10#1#0#0p=3g00YTR7%K2%K3=:703:p=jA:7309:72p=X%K3=:70p>08f3R8/I2?h30p>07%10#0#1p>0P%10#0#0#1p=W%10#1#0#0#1#0p>06%00#1p>05%00#0#1#0#0p=[%Z0,I3p>0N%83/U0p>02g00Z]R9A:9307:2p=S%03#8,U2=:90p=wf4R:#0#8/U8%02#8/U3=:905:9p=g1I:8?h23=:90p=71U23=:90p>0L%02#8/U3=:90p=v1U:81U23=:905:9p>0K%Z8,I:?h23=:90p=5%18#0#0#0#Z,I:?h23=:90p=R%08#Z,I:?h23=:90p=V%Z8,I:%83#67h2=:90p=nP7P7P3P0COp=uP:P820023P0H0=p=Lg00[hR;?M30#~p>0@A};30p>0?P1P8P2P3CO=<:0p>0HA<823/C0p>0>f6R<f5R=;<:A<823/C0'Cp>0If7P1P<AM;=:#~A};82CO;<3/C0p=\&0R5R0,l1R3g00]6R8#a#]#;#?#4%y5R55J0R2;<2%a8#@#H#A#4R=g00VWR:g019=g00^GR<#2R>#2R?#2R@#2RA#2RB#2#oRC#o#q#{$09RD#KREg00`[RF#6RG'bRH%18RI#1RJ#1RK#1RL#1RM#1RN#1#iRO#1RP#1#ERQ#1#iRR#1#xRS#1#E#iRT#1#ERU#=#N#fRV#6Cd/P55J0RW=<3WS01AJ0=5RX=<3XS02%A8#Q#E#B#s=J05RY=<3YS03P:g019oS04%2D#o#{#m#mRD#KRZ/bGR[PZCd%K?R\/DZ/IFP>P:PGH0:/P5'P9J0=R]=<3]S05%TMR^/rZP6g00aYS06P6P<PAPZC|1b[GCd/P5'P9J0=R_=<3_S07g00][S08%Z8#6S09<0<Z/D^%88R`#6Ra'r/P59J0=Rb=<3bS0:%a8#G#B#A#4=J05Rc=<3cS0;g00^fRd$0QRe%`8$0;#4Rf%08Rg#8Rh%a8#H#9#Y#4Ri%K<Rj%0gRk#0Rl#1Rm#1Rn#0S0<#FS0=#0S0>#ZS0?#6'DRo1DjZ%0lRp#1Rq#1Rr#1Rs#1#k#6Rt'DRuPo%1gRg#0Rv#=Rw#TS0@PGPG%1kRk#0Rx#0Ry#0Rz#0S0A#0S0B#0S0C#ZS0D#6,DjR{%oD#q$09#m#m#mRD%6i%0qS0E#FS0F#FS0G#9#_%e8#G#9#?#4Rq#6%2D#qR|%2|R|%2|R|%6fS0H1bG[S0I%Tm'bR[,ba%q|R|#K%2|R|%2|R|%2|R|%2|R|%2|R|%2|R|%^8#Y#Y#4R}#6R~%>8#Q#3#B#_%2|#o#{R|%2|R|%2|R|%2|%y73j3j9XGG9XGG9XGG7XG7Xa3j3j3j5XG3X+083j3X7X{+08PG%`8#Y#4S0JPC%=KS0K#0S0L#k#6,DjS0MPG%`8#;#4PCPoPG%`8#?#4S0NPCPoPj%1yRyPC%1nRn#FRK#E#Q#TPj%9yPCQ0HPjPzPCP[PjQ0CPCg00_oRy%TRRR;p[PjPnPCPRPj%0KS0CPC%1xRx#TPjQ0<PC%18#F#?#Q#]#_Pj%0mRm#1RKPCPGPj%0mRm#0S0<#0S0H#0RRPCQ0IPj%=KRKPCPZPjQ0>PC%0pRn#0R[#1R|#1#Q#>#TPjPmPCPG%8P9cZFPj%=M#kPCP\H07PjQ0DPC%1v#F#kRv#6,DjPjPRP>%TnRRPjPKPC%0IRI#1RK#1RM#1#F#3RZ$0P#Q#9#;#E#B#9#Q#H#;#E#;#]PjQ0?PC%eZ#;#G#B#9#G#>#;#W#;#3#;#G#TPj%=sPC%FS#3#3#3#3#3#3#@Pj%9rPC%0T#i#iPj%=NPC%0IRI#1RN#1#G#G#G#G#G#_Pj%1nRn#9PC%=xRx#?#WPj%F[RT#FRrPCP~Pj%=|PCPGPjPnPCP{PjQ0EPCQ0MPjQ0GPC%1kRk#1#F#kR{#6,DjPG%`8#G#4PCPGPG%`8#B#4RnPCPGPG&068#A#B#4R|PA%1U#x#i#fRU#6PG%`8#@#4PCQ0@PG%`8#3#4RSPCPoPGPfPA%TgPjQ0BPCPGPjPxPCPGPj%=kRkPCPGPjP{PCPGPjQ0=PCPGPjQ0CPC%1gRg#=R{#kRx#6,DjRsPjQ0HPCP:P?PFPCH0ORZPjQ0FPCPGPjPTPCPGPj%=LPC1DjRRRPjQ0LPCP\Pj%0JRJPC%6hRLPj%0JRJ#0RT#0RPPCP~Pj%=MPC%18#F#;#@#W#_Pj%=KRKPCPsPj%=NPCPZPjPkPCPGPj%0wRkPCPGPjPvPCPEPjPxPCP\PjQ0<PCPTPjQ0APCPGPj%0IRI#FRxPCPLPjPgPC&058#]$0;#E#_PG%[8#A#3#]#sPAApyGH%9O#N#N#N#4RO%FrRr#9Ry#=#9RH#0Rg#?#N#N#4Rv5c\AcEVUPjQ0KPCPGPjPPPCPGPjPKPCPGPjPxPCPGPjP{PCPRPjPwPC&058#@#?#;#_PjPzPCPLPjP[PC%8lRl#6R[,DjPjPTPC%08#x#A#E#;#_%8pRp,zj%9g#N#N#49cjO20NjHRg%8HRH+04PjPFPCPLH07PjPlPC%K>PjPpPCP\Pj%8IPCPG%K@R@?cOv%KARI?cOvPgPH1I@F%8kH03PgPH1IIFPpH031z@l1zIl%aJ#N#4,IG%a8#H#N#4+04202yf%38#>#?#;Pn%38#>#W#9Q0J%38#>#W#3Q0N%38#>#>#HPS%38#>#A#?P|%38#>#3#>&068#@#]#4%38#A#Q#?#f%38#A#W#3#fR|P|%[8#A#W#3#fR|%[8#A#A#?%[8#3#B#3%^8#9#@#4PG%e8#B#]#E#4RSPC%6SPG%e8#B#E#G#4PA%KBRB%[8#A#@#B%e8#B#E#]#4%[8#A#E#3%e8#G#9#B#4%[8#3#9#3%e8#G#9#;#4%[8#3#B#?%18#H#3#H#91IG}@0M[?%a8#W#>#A#9%^8#Y#Q#4+02%18#H#@#;#H#f%^8#Y#>#4R[PGP[PCP@%18#H#@#;#3%^8#Y#3#4%18#H#@#Q#?%^8#Y#E#4R@PGP@PC%8rRr#6%18#H#@#?#9%^8#;#;#4%18#H#@#W#3%^8#@#@#4RC%18#Y#?#N%8Q9cB`1UFr%y93S5wCDgD7DgD740L3S7v}5wq3vDgD7D73v5w|I0KDgDgDg3S3S3S3SD7D7D73S3SD5D5D5D5D5D5D5D5D53SD7DRDVD5DnD7D7D5D5D5DVD5DVDRD5D5D5D5D5D5D5D7DVD5D5D7D7D7D7D7D7D5DRDRD5D5DnD5DnDnD7DnD5D73SDRDVDVDVDRDRDVDRDVDRD5DRD7D7D7N<0J-01dR|;<|Rq1l11R}/l1RCP}P1P1P1PiPfCOPhCORh;<hRf1l77Ri/l7R9PiP71uouPGCORu;<uRr%Q8#>#;#>#s=J05R8=<38RB'CR`'CRQ'CR@'CR['CR?'CRS'CRn'CRy'CRJ'CP3P2Q01PJP3PWQ02PyP3PXQ03PnP3PYQ05PSP3P]Q07P?P3P_Q0:P[P3PbQ0;P@P3PcPqPQPeP|PfP`PCPhPrPBP9Pu20038DLDLDLDLDLDLDLDLDLDLDLP3P0P01l;0R;g00bKRug01:a3MRBP0PBP2P3P0P0g01;[9M;uR2P0P2PWP3P0P0g01<U9M;uRWP0PWPXP3P0P0g01=O9M;uRXP0PXPYP3P0P0g01>I9M;uRYP0PYP:Q04g00dRRY=p4GRXPYCdAt4\Y/IFP>P:PGH0:/P5'P9J0=P3P0P0g01?C9M;uR:P0P:P6Q00P^PYCdP6Q06P6P<PAPYC|1bXGCd/P5'P9J0=P3P0P0g01@=9M;uRXP0PXQ08Q09<0<Y/D^/ra/P59J0=P3P0P0g01A79M;uR=P0P=PcPeg00eLg00fDPDg01B1g01BlI0Gg01CgRD-01dPCP}P1P1P1&0FD&0EDCO&0DDCOPhP9PiP7&0AD&0BD'u&0CDCOPiP7At4jY/Dt,uoPGCOP3P0g01Dc9M;uRu-0@020?0uP8I0HH0>K0IG\G\G\G\G\G\G\G\do"). Qed.
End VP2.
