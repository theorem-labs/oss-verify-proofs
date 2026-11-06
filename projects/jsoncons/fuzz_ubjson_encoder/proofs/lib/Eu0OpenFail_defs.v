(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Eu0MainEntry SymDriveH4 Eu0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_sC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_lC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2PXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4srG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4knG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4scG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4srH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4knH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4scH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rI3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4srF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4knF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4scF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4srH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4knH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4scH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3rI4C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond06C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3srHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs3knHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs4scOFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Eu0OpenFail_defs2rIC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition STOPS : list Z := [0xae008; 0xae588; 0xaeafc; 0xadf0c; 0x9d124; 0x9d2b0; 0xa11dc; 0x9d974; 0xa2b78]%Z.
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
Definition IHI : Z := 0xee000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x34a4c sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0xaefb4 srB0 [] knB0 39.
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
Definition ssC0 : sym_state := SS 0xa3354 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xa3354 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xa3ec4 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xa3354 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xa3354 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xa3354 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0xa3824 srI0 [] knI0 263.
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
Definition ssI30 : sym_state := SS 0xa3824 srI30 [] knI30 263.
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
Definition ssH40 : sym_state := SS 0xa3354 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0xa3824 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0xa2b78%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0xa39f4%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x12b82, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0xa2b78%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x9d974%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0xa2b78%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0xa4414%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0xae008%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0xa2b78%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x9d974%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0OpenFail_defs ()) ["FPX_1"] "p%0p%1p&0p;1p;2p;3p;4p;<g0000k10RTg000Pj2fTg0010j10Tg001Uj11Tg002:j1@Tg002Xj18Tg003fj12Tg004Ej1CTg005Sk30HTg006aj17Tg007?k10<Tg007_j3<Tg0089k10MTg008[k306Tg009ij3kTg00;9j2FTg00<Hk40QTg00=Vk20=Tg00>fk20ETg00@6k40DTg00AFk30:Tg00BVj2OTg00Cfl<~Tg00E<j2^Tg00E^k40CTg00Flj4}Tg00H>j2:Tg00HYj2TTg00I3j3YTg00IPj1cTg00J\j3{Tg00L1j1zTg00MBk102Tg00NQk101Tg00Oaj1yTg00Q1k105Tg00RAk10ATg00SPj1|Tg00T_k309Tg00Umj4gTg00VMj34Tg00Vmj3aTg00X=k407Tg00XXk30ITf0R0#0#1#1#0p=p%10#1#1#1p=J%00#0#0#7p=5%20#2#2p=q%20#2p>0B%20#2#2#2p=W%20#2#2#2#2#2#2#2p=x%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=_%70#8p=Ag00Y5R1f1R2<090p=\g00YaS00g00ZAS01P2P0C}p>0>g00[3R3?420p=ng00\ER4f2R5P2P0Cgp=E%10#0p==%00#1p=9%10#1p=L%10#1#0#0p=V%10#0#0#7p=r%00#0p=6%80:0912p=Z%10#0#0p=?%00#0#0#1p=U%00#@p>08%00#0#0#0p=H%00#0#7#8p=[%10#1#1#1#1#1#1#1p=lB06120p=`g00\cR6%C2;40p>0@%C5%C2=460546p=Df3R7%C2=4609465546p=of4R8A462094659467546p=S%C7A46209465546p>0?%00#0#0p=;1F75?a20p=K%00#0#0#0#7p=Q%05#@,F7?a20p=G%10#0#1#1p=w%10#0#0#0p=v%00#1#0#0p>0G%00#0#1#0p=j%00#0#1#1p=i%10#7p=u%809a52p>0F%10#1#1p>04%00#0#1#1#0#0#1#1p>03%00#0#0#0#0#0#0#0p=I%@0,F2p>0P%72/O0p>0;%00#7p>0O%70,O2p>0Ng00^1R9A4920745p=R1O52=490p>001F87?a52=490p=>%08#7/O7%05#7/O2=490549p=m%05#7/O2=490p>0L1O871O52=490549p>0KA4920949594979498p=B%@7,F8?a52=490p=3%07#@,F8?a52=490p=M%17#0#0#0#@,F8?a52=490p=XP4P4P2P0Cgp=eP5P4P2P0Cgp=hP7P6P6P6P5P2CgP0Cgp=PP5P6P2P0Cgp=sA4920p>0Jf6R:f5R;P8P7P5P2P0H07H07p=tP8P71T52P0H07p=]g00_AR<?Y20p=dB0I<20p=bA<:;8A<752/:0':p=N&0R3R0,f4R7g00`TR5#0R2#1R;#0R:#0S02#0R8#1R=#0S03#1S04#p#J#5R>g00a9S05%@5#8S06g00aeR?#2R@#2RA#2RB#2RC#2S07#qRD$0B#W#x#_S08#q#x#_#_#_#_RE#CRF40H%15RG#1RH#1RI#1S09#1RJ#ARK'\%75S0:#8R5+0>&0<3R3'n5E0RL;<Lg00bDRM$0MRN%1;S0;#=S0<#1S0=#0S0>#JS0?#0RO#9#LS0@#5RP%72RQ%V=R=#J#=#rRR%C?RS%02R2#0RT#1RU#1S0A#0S0B#6S0C#0RV#@RW'ZRX1\SF%0TRY#1RZ#1R[#1R\#L#@#8R]'\S0DPX%08R8#AR^%12R2#0R_#1R`#0Ra#LRb#?#URc#0#ARdP5&08VRV,ZSRe&0BE#W#_#_#_RE#2#WS0E#2S0F#2S0G#WS0H#2S0I#2S0J#2S0K#2S0L#2S0M#2S0N#q#xS0O#2S0P#2S0Q#2S0R#2Rf%8RS0SPe%0ZRZ#6S0T#6Rg#H#[S0U%0GRG#0S0V#1S0W#=#9Rh#9S0X#1S0Y#1S0Z#=S0[#6#5S0\#8S0]%2f#WRi%2iRi%2iRi%A`S0^%1JRj#1#lS0_#1Rk#1#JS0`#1#lRl#ARmP5%WiRi#C%2iRi%2iRi%2iRi%2iRi%2iRi%2iRig00cZS0ag00dFRn#8Ro1`FoRp'`S0b%AUS0c'`Rq806mS0dPq%8PRr%1c#AS0eP5PdPo1`poS0fP5Pp%qi#xRi%2iRi%2iRi%2iS0g&0<6Ri+0@3DCoDSDS3D3D3DDS3DCoH0?Po%1ORO#0Rc#1S0h#1#5S0iPD%;IS0j#0S0k$08,ZSS0lCKS0mPo%1ORO#0S0n#QPDPXCKS0oPo%1OS0p#QS0qPDPXCKS0rPS%0URU#1RO#1S0s#6PDPoCGS0tPS%0URU#0S0u#0S0v#0RIPDQ0bCGS0wPS%;OROPDPFCGS0xPSPVPD%0YRV#1Rs#6Rt#V#w#ACKS0yPS%?UPDPoCGS0z%7k9kFnS0{PS%;JPD%CARJCGS0|PS%0_R_#0S0}#0S0~#0S10#0S11#@RkPD%1:RU#0Ru#6Rv#@S12,ZSCKS13PS%@IP@%AVRICKRwPS%@OPD%1GRG#1RO#?#VRx#1#9#9#V#U#w#V#v#U#L$0G#p#J#9#w#=#ACKRy1FSWS14%jx#V#p#9#H#U#L#9#i$0G#w#p#i#U#u80FDS15PS%6\PD&04lRl#i$03$03$03#9#ACGS16PS%;[PD%1l#J#lRl#0#l#l#ACGS17PS%6jPD%?hRh#L#i$03#[CGS18PS%0tPD%6aRa#=#j#9#ACGS19PS%1US1:#HPDQ00PAPnPDH0QRUPS%0VRV#6S1;#6Rt#@PD%0HRH#1Rj#1S1<#0R[#9R\#1Rx#1S1=#0RW#0Rz#9R{#1R|#QR}#8R~CKS1>PS%?VPDPoCGS1?PS%?sPD1ZSkRkCGS1@PS%?ZPDQ0lCGS0lPS%@gPD%12R2#1Rg#0RZ#6Rs#@S1A,ZSCKS1BPS%?uPDPoCGPS%6vPDPoPSQ02#1RvPDPoPS%;vS02PDPoPSQ03#6PDPoPS%08Rv#6PDPoPSPgPD%A;R;PSPsPD%1[#i#=#=#=#[S03PS%02R2PDP5PS%62R2#0R[PDP~PSP`PD%pb#J#APSPaPDPrPS%1_S1C#;S1DPD%;=R=#U#[Po%0cRc#1#5PDPoPo%QcS1EPDPoPoQ0?#1Rc#vR_#5S0?PC%1l#JRl$04#l#uRb#8Po%0cRc#9R`#1#5PDP^Po%Q`S1FPDPXPoPPPCP;PSQ10PDPoPSPaPDPoPSP[PDPoPSQ1APDPoPSQ0CPDPoPSQ0A#1S0A#;S0CPDQ0;#;S0;$08R[,ZSRaPSQ0vPDPUPSQ0TPDPoPSQ1;PDPoPSQ09#;PD1\SIS09PSQ0kPDPJPS%;jPD%8QRjPS%6HRH#0S0kPDP~PS%;OPDQ04#1#p#U#[PS%6GRG#0S04#0ROPDPaPSQ0W#;PDPUPSP2PDPoPSPvPDPoPSQ12PDQ08#CR2PSP[PDPJPSQ0uPD%AHPSQ0~PDPoPSQ0V#0R[#6S0VPDPjPSQ0<#6PD%1GRG#1#j#V#[PoQ0Y#0RU#0Ra#0#LRI#rPCQ0a1`2o806oQ0_#H#I#I#I#5R;%6tRt#HR`#;#HRs#0Rg#v#I#I#5Ru5kJ%;l#I#u=k2bPSQ0jPDPoPSQ0kPDPoPSQ04PDPoPSQ0VPDPoPSQ0;PDQ09PSP8PD%0G#=#9#i#[PSQ0}PDPjPSPVPD%7TRT#8RV,\SPSPHPD%1ZRZ#i#j#=#[%7YRY-0=S%Hg#I#I#59kS;20PSsRg%7sRs+0EPSPnPDPjCKPSPTPD%C@PSPYPDPJPS%7[PDPo%CBR[?k;u%CCRj?k;uPgPs1F[n%7vH0DPgPs1FjnPYH0D20=[T20=jTQ0>#0#I#5,Fo%;O#H#5+0E20;`PQ0@#=Q1EQ0h#;Q0iQ0n#?Q0qQ0p#?Q1F%1c#HQ0?%=_Q0=#=#j#=#HR_$0O%u_Q0X#0#JR_#Q%0\#JR\#0#9#5%1\#9#5Po%1_#5R_PD%8_Po%5IPCQ07#CRI%1a#j&04URU#Q%?UQ0Z#0RU#9Ra#QR_PoP_PD%1WRW#0R_#6R\#1#5Rc#8%?a%1U#=#5RU1FoU@0:VAQ0\Q0[#1RU#H+0N%?U%0h#=#9#5%0x#I%9{#5R{1Fo}@0:VA%v|%1zRz#0R|#6#5+0;%1|R|#;#u%1|#5R|PoP|PDP[%1zRz#0R[#;%1[#5%Vz%Q\R\PoP\PD%7tRt#8&04_#5R_1Fo_@0:VB%?W#HQ1=#L#=#9#5RW+0;Q1<#?#I#5Q0:Q0`#75kI1Ont&0<93R600W3R600cD>DmD>4003R:00{}Dm3R40LD>DmD>D>I0KDmDmDmDBDBD>D>D>DBD3D3D3D3D3D3D3D3D33RD>D3DMD3D3D>D>D3D3D3D3D3DMD3D3D3D3D3D3D3D3D>D3D3D3D>D>D>D>D>D>R{D3DMDXDMDXDMDXD3D3DMDXD33RDBD33RDBDBDBDBR}M<~,^MRc;<cRW1f44R9/f4R41eRP=h9QRR;<RRt1f66Rn/f6RI/f6RVPnPXQ0DPdCP=sI5RB;<BR_AE0>3R\=<7\RzPPPQ%?=#rR=PXPXPXP^PoPoPkQ0g#2R[%8=PkQ0UQ0]%2[#WR|%2|R|%2|R|Pr1`5qPo%W|R|#C%2|R|%2|R|%2|R|%2|R|%2|R|%2|R|P~P5Q03PoPoPoPoPoPoPo%q|#xR|%2|R|%2|R|%2|00@i3DCoDSDS3D3D3DDS3DCoH0?R|Q0mQ0oQ0rQ0tQ0wQ0xQ0yQ0zQ0{Q0|Q13PwQ15Q16Q17Q18Q19Q1>Q1?Q1@Q0lQ1B00J{DBDBR{5RyDBDBDBM<~,^MR~=<N~RA1e=P=h9QRx=<4xRhPnPXPXPoCPRU=<IURa%?Z#w#=#r=E03RZ=<7ZR`20>KFg00ddROg00eDRjPOP?PCPFH0CQ0fC}/n3'n9E0>RT=<7TRYPPPQQ02#v#j#rRsPX1\S]RgPXP^PJPFPePE%8sPeQ0UQ0]Q0EQ0FQ0GQ0^PmPFQ0H#CQ0IQ0JQ0KQ0LQ0MQ0NPoQ0cPrPdPoPJPoQ0fQ0bPpQ0OQ0PQ0QQ0R00@i3DCoDSDS3D3D3DDS3DCoH0?P}M<~,^MR}=<N}Ri1esP=h9QRs=<4sRpPnPXPgPJCPRJ=sIFRF=<VFRgQ1:#?#H#U#5=E03Re=<7eRvPPPQP=PXQ0s#L#@,ZSR=PXP^PoPoPkP|Q0mQ0oQ0rQ14%7:80F@PSQ1CPDQ0ePSQ1DPDPrPSQ0}PDPqPSQ11PDQ0dPSQ0APDPmPSQ0CPDQ0^PSQ0BPDQ0SQ0tQ0wQ0xQ0yQ0zQ0{Q0|Q13ARwy{DBDBDXDMDXDMDXDMDXDBM<~,^MR{=<N{RyPnPXP=PoCPR==<I=Rw/:`RD,:hRm':Rq,:zRr':R@':R:':R|':Rk':R^':RQ':RP':Ru':R;':RH':RG':R8':P7PLPWP8PNPcPtPGP4PRP_PHPVPBPzP;1T7\R;PAPu1TN~PhPP1T4xRPPaPQ1TIUP`P^1T7ZR^PYPk1T7TPiP|PNP}PpP:P4PsPgP@PVPFPvPrP7PePzPqP;PyPm1TN{PhPDPPPwP`1TI=P^FtFtD]D]D]D]FtFtFtD]D]D]D]P71f<0R<g00f6R^g00gG3YR`,d0#c1b0`5E0Q05Q06g00hVR`40H/\K00>5/n39E0>PNg00idg00k45{fg00lDRf,^MP4%zf&02f'e&01f5h9PRPVPn%yf&05f&0AfCP%|f5sIPnPXB091S`/\]PdCP=sI5P7g00mT9Y<^R5,d0#c1b055E0P\PNg00ncg01035{[g011CR5,^MP4%z5&025'e&0155h9PxPIPn%y5&055%|5CPPUP7g012S9Y<^RU,d0#c1b0U5E0PZP7g013b9Y<^RU,d0#c1b0U5E0Q00Q01PKP`C}POPjPOP?PCP`H0CB061`o/`oC}/n3'n9E0>PNg0151g016A5{Eg017QRE,^MP4%zE&02E'e&01E5h9PsPVPn%yE&05E&0AECP%|E5sIPIP6PJP`CgP7g018a9Y<^R`,d0#c1b0`5E0PeP7g01:09Y<^Re,d0#c1b0e5E0P\PNg01;?g01<O5{[g01=_R[,^MP4%z[&02['e&01[5h9PxPIPn%y[&05[%|[CPP=g01>o9Y<^R^,d0#c1b0^5E0=<7ZFNFNFNFNFNFNFNFNFNdo"). Qed.

Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xaefb0%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0xae008%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xae008%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xaeafc%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xae008%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xae008%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xae008%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xa2b78%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x9d974%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0OpenFail_defs ()) ["FPX_1"] "p%0p&0p;1p;2p;3p;4p;<g0000k10ITg000Pj2`Tg0010j10Tg001Uj11Tg007?j1pTg007_j3=Tg003fj12Tg004Ej1CTg002Xj17Tg00Flj4ZTg00;9j2?Tg01@>j4|Tg00E^j4xTg002:j1MTg005Sj3wTg006aj19Tg0089k10HTg008[j3lTg009ij3XTg00<Hk40FTg00=Vj2tTg00>fk200Tg00@6j4~Tg00AFj3qTg00BVj2RTg00Cfm<0ATg00E<j2}Tg00Umj4ITg00H>j2ATg00HYj2{Tg00I3j3HTg00T_j3nTg00J\k30?Tg00L1k10>Tg00MBk10=Tg00NQk10<Tg00Oak10;Tg00Q1k10:Tg00SPk109Tg00VMj3:Tg00Vmj3]Tg00X=k404Tg00IPj1zTg00XXj3yTf0R0#1#0p=6%10#1#1#1p=E%00#1#1#0p=U%00#0#0#9p=5g00\ER1f2R2f1R3P0CIp=D%00#0#0p=<%00#0#0#0p=>%00#1p=4%20#2p=g%20#2#2#2p=m%20#2#2#2#2#2#2#2p=v%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>01g00Y5R4?l30p=Y%10#1#1#1#1#1#1#1p=\%10#1#1p=i%00#0#0#0#0#0#0#0p=F%10#9p=hg00[3R5?:30p=J%00#9p=d%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=cAn430p=@%90#7p=Kg00ddR6g00ZAS00P3P0CZp=s%00#0p=;%10#1p=[%10#1#0#0p=b%00#0#1#0p=W%00#Mp=a%00#0#9#7p=V%00#0#0#0#9p=Q%00#0#1#1p=Og00\cR7%C2%C3=:703:p=_A:7309:72p=P%C3=:70p>03%10#0#0#0p=f%10#0#1#1p=uf3R8/?2?]30p>02%10#0#0p=L%00#1#0#0p>0G%00#0#1#1#0#0#1#1p=k%M0,?3p>0E%93/R0p=r%90,R3p>0Dg00^1R9A:9307:2p=B1R23=:90p=jf4R:/?8?]23=:90p=8%0:#9/R8%02#9/R3=:905:9p=^%02#9/R3=:90p>0C1R:81R23=:905:9p>0B%M8,?:?]23=:90p=3%08#M,?:?]23=:90p=T%M8,?:%93#77]2=:90p=e%18#0#0#0#M,?:?]23=:90p=NP7P7P3P0CIp=oP:P81{23P0H04p=Gg00_AR;?H30#zp>08Ay;30p>07P1P8P2P3CI==:0p>06A=823/A0p>05f6R<f5R=;=:A=823/A0'Ap>0@f7P1P<AH;=:#zAy;82CI;=3/A0p=S&0I5R0,`1R3g00`TR8#0R2#1R=#0R:#1R<#1#6R>#1R?#E#U#5%p5R55D0R@;=@%<>#>#4#5R>g00YaRAg01APg00aeRB#2RC#2RD#2RE#2RF#2S01#2#gRG#g#m#v$01RH#CRIg00dFRJ#7RK'YS02%18RL#1RM#1RN#1S03#1RO#1RP#1#\S04#1RQ#1#ES05#1#\RR#iRS#1#E#\RT#1#ERU#<#F#hS06#7CZ/J55D0RV==3VS07AD0>5RW==3WS08%4?#4#E#6#d=D05R?==3?S09PAg01BBS0:%2H#g#v#c#cRH#CRX/YKRYPXCZ%CDRZ/@X/?JPCPAPKC|/J5'J9D0>R[==3[S0;%KOR\/sXP6g00eDS0<P6PBPFPXCx1YYKCZ/J5'J9D0>R]==3]S0=g00a9S0>%M8#7S0?;wX/@\%98S0@#7R8's/J59D0>R^==3^S0A%;:R:#1R_#4R`#U#E#5=D05Ra==3aS0Bg00bDRb$0HS0C%1=Rc#6S0D#1S0E#0S0F#ERd#0Re#4#[S0G#5Rf%92Rg%b_R_#;#4#W#dRh%CBRi%02R2#0Rj#1Rk#1Rl#0S0H#;S0I#0S0J#MS0K#7'@Rm1@iX%0jRn#1Ro#1Rp#1Rq#1#a#7S0L'@S0MPm%0:R:#KS0NPKPK%12R2#0Rr#0Rs#0Rt#0S0O#0S0P#0S0Q#MS0R#7,@iRu%gH#m$01#c#c#cRH%7h%0oS0S#;S0T#;S0U#>#V%0LRL#0Ro#1Rv#6#4Rw#4S0V#1Rx#1S0W#6S0X#;#5S0Y#7%2H#mRy%2yRy%2yRy%7fS0Z1YKYS0[%Kk'YRY,Y8%myRy#C%2yRy%2yRy%2yRy%2yRy%2yRy%2yRy%0MRM#1Rz#1S0\#0R{#4S0]#1S0^#1S0_#0S0`#0S0a#4S0b#1S0c#QR|#7R}%1{#O#6#6#6#V%2y#g#vRy%2yRy%2yRy%2y%p73_3_9PKK9PKK9PKK7PK7P83_3_3_5PK3P+033_3P7Pu+03PK%1eRe#0Ry#1R{#1#5S0dPG%<NS0e#0S0f#a#7,@iS0gPK%1eRe#0RN#QPGPmPK%1eRe#QS0hPGPmPi%1sRsPG%1rRr#0R~#[#f#O#KPi%>sPGQ0ZPiPtPGPYPiQ0QPGg00cZRs%KRRR;lYPi%1lRlPGPRPi%<lS0QPG%KrPiQ0HPG%1_#E#4#VPi%0kRk#1R_PGPKPi%0kRk#0S0H#0S0Z#0RrPGQ0[Pi%<_R_PGPXPiQ0JPG%0nRl#1RR#;RY#b#u#KPiPkPGPK%9Q9XXJPi%<O#aPGPZH02PiQ0RPG%;<#aR<#7,@iPiPrPC%KlRrPiP_PG%1LRL#1R_#L#bRO#1#4#4#[#>#U#E#W#>#4#[$0G#U#E#4#u#6PiQ0KPG%0O#4#U#O#W#>#O#6#6#U#6#4#U#b#U#O#KPi%<qPG%OS#k#k#k#4Pi%>pPG%0T#\#\Pi%<PPG%LwRw#[#O#k#VPi%;YPG%;~R~#6#W#4Pi%0lRl#;RY#;RPPGP}PiPlPGPKPiPRPGPuPiQ0SPGQ0gPiQ0UPG%12R2#6Ru#0#aRR#7,@iPK%0yRy#1#5PGPKPK%QyRyPGPKPK%1dRd#fRT#5RpPF%iU#\#hRU#7PK%0dRd#4RS#1#5PGQ0NPK%QSRSPGPmPKPfPF%K=PiQ0PPGPKPiP~PGPKPi%<2R2PGPKPiPRPGPKPiQ0IPGPKPiQ0QPG%<cRc#aRR#7,@iR~PiQ0ZPGPAPDPJPGH0FR=PiQ0TPGPKPiPYPGPKPiQ03#<PG1@irRrPiQ0fPGPZPi%<zPG%7gRzPi%;MRM#0RYPGP}Pi%<_PG%1`#4#f#4#VPi%;LRL#0R`#0R_PGP~Pi%<vPGP=PiP2PGPKPi%0:R2PGPKPiP<PGPIPiPRPGPZPiQ0HPGPMPiQ0OPGPKPi%0oRo#;RRPGPzPiQ0D#;PG%1LRL#1#W#b#VPK%0xRx#0R<#0#[R=#6#dPFQ029lsKQ04#>#F#F#F#5Rs%;PRP#>Rv#<#>R~#0R}#f#F#F#5Rq5XZQ06=XIUPiQ0ePGPKPiPYPGPKPiP`PGPKPiPRPGPKPiPcPGPrPiP:PG%0L#6#4#O#VPiPtPGPzPiPlPG%9jRj#7Rl,@iPiPMPG%1uRu#O#W#6#V%9nRn,ti%>}#F#F#59Xis20Ei~R}%9~R~+00PiPJPGPzH02PiPjPG%CCPiPnPGPZPi%9oPGPK%CERo?Xsq%CFRz?XsqP}P~1?oJ%92C~P}P~1?zJPnC~1toj1tzjQ0F#0#F#5,?K%<_#>#5+001rvfQ0G#6Py%<{Q0d%LNQ0h%LePS%1d#>Pp%6TQ0E#6#W#6#>RT#d%hTQ0V#0#ERT#QQ0]#0#ERp#0#4#5%1p#4#5PK%1T#5RTPG%7TPK%5=PFQ01#CR=%1<#W%ixRx#Q%LxQ0W#0Rx#4R<#QRTPKPTPGQ0`#1RT#0Rp#;Rd#1#5RS#7%L<%1x#6#5Rx1?Kx?qlDQ0YQ0X#1Rx#>+0D%Lx%0w#6#4#5Q0^#0#FQ0b#4#5Rw1?K|?qlDQ0c#fQ0a#1RD#0Rx#;#5'r%1xRx#<#h%1x#5RxPKPxPGPo%1DRD#0Ro#<%1o#5%bD%QdRdPKPdPG%9PRP#7%ip#5Rp1?Kp?qlE%LT#>Q0_#[#6#4#5RT'rQ0\#L#F#5Q0@Q05#95X=1RJP%p93B5jT3B5jSD8D^D83j3B9jw|D^3B40CD8D^D8D8I0BD^D^D^3B3B3B3BD8D8D83B3BD3D3D3D3D3D3D3D3D33BD8D3DTD3DeD8D8D3D3D3D3D3DTD3D3D3D3D3D3D3D3D8DTD3D3D8D8D8D8D8D8D3DNDNDND3DeD3DeDeD8DeD3D83BDNDTDTDTDNDNDTDNDTDND3DND8D8D8N<0A,}bRw;=wR|1`11RS/`1RTPSP1P1P1PhPfCIPgCIRg;=gRf1`77Rh/`7R9PhP7Q0M,omPKCIRP;=PR=%Lu#u#6#6#d=D05Ru==3uRl'ARE'ARp'ARG'ARd'ARD'ARo'ARx'AR<'ARe'AP3P@Q07PeP3PVQ08P<P3PWQ09PxP3P?Q0;PoP3P[Q0=PDP3P]Q0APdP3P^Q0BPGP3PaP|PpQ0CPwPfPEPTPgP=PlP9PP1{3uDGDGDGDGDGDGDGDGDGDGDGP3P0P01`;0R;g00f6RPg01C43HRlP0PlP@P3P0P0g01DB9H;PR@P0P@PVP3P0P0g01EP9H;PRVP0PVPWP3P0P0g01F^9H;PRWP0PWP?P3P0P0g01Gl9H;PR?P0P?PAQ0:g00hVR?=l4KRWP?CZAn4Z?/?JPCPAPKC|/J5'J9D0>P3P0P0g01I:9H;PRAP0PAP6Q00P\P?CZP6Q0<P6PBPFP?Cx1YWKCZ/J5'J9D0>P3P0P0g01JH9H;PRWP0PWQ0>Q0?;w?/@\/s8/J59D0>P3P0P0g01KV9H;PR>P0P>PaQ0Cg01Ldg01N360?Hg01OBRH,}bPTPSP1P1P1&0>H&0=HCI&0<HCIPgP9PhP7&0;H&0:H'o&09HCIPhP7An4i?Q0L'@,omPKCIP3P0g01PR9H;PRP-0802070PPuI06H05K0@GSGSGSGSGSGSGSGSdo"). Qed.

End FPX_1.
