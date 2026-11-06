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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Es0MainEntry SymDriveH4 Es0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0OpenFail_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_sC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_lC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndK4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr5mulop01K47Corelib4Init9Datatypes3nat01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2PXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4srG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4knG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4scG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4srH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4knH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4scH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rI3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4srF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4knF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4scF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4srH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4knH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4scH4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3rI4C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond06C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3srHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs3knHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs4scOFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@Es0OpenFail_defs2rIC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition STOPS : list Z := [0xac48c; 0xaca0c; 0xacf80; 0xac390; 0x9b5a8; 0x9b734; 0x9f660; 0x9bdf8; 0xa0ffc]%Z.
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
Definition IHI : Z := 0xec000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x34544 sr_main [] kn_main 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0xad438 srB0 [] knB0 39.
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
Definition ssC0 : sym_state := SS 0xa17d8 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xa17d8 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xa2348 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xa17d8 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xa17d8 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xa17d8 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF : stdio_res := Eval vm_compute in sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0xa1ca8 srI0 [] knI0 263.
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
Definition ssI30 : sym_state := SS 0xa1ca8 srI30 [] knI30 263.
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
Definition ssH40 : sym_state := SS 0xa17d8 srH40 [] knH40 231.
Definition rH4 := Eval vm_compute in run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 : stdio_res := Eval vm_compute in sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4.
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0xa1ca8 srI40 [] knI40 263.
Definition rI4 := Eval vm_compute in run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4)).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0xa0ffc%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0xa1e78%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x12b82, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0xa0ffc%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x9bdf8%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0xa0ffc%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0xa2898%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0xac48c%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0xa0ffc%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x9bdf8%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0OpenFail_defs ()) ["FPX_1"] "p%0p%1p&0p;1p;2p;3p;4p;<g0000k10OTg000Pj2iTg0010j10Tg001Uj11Tg002:j1ATg002Xj1:Tg003fj12Tg004Ej1CTg005Sk30ETg006aj19Tg007?k10:Tg007_j3;Tg0089k10HTg008[j3wTg009ij3gTg00;9j2JTg00<Hk40MTg00=Vk20<Tg00>fk20CTg00@6k40BTg00AFk308Tg00BVj2QTg00Cfl<}Tg00E<j2^Tg00E^k40ATg00Flj4|Tg00H>j2<Tg00HYj2UTg00I3j3]Tg00IPj1aTg00J\j3zTg00L1j1yTg00MBk104Tg00NQk100Tg00Oaj1xTg00Q1k102Tg00RAk10@Tg00SPj1{Tg00T_k307Tg00Umj4eTg00VMj34Tg00Vmj3mTg00X=k405Tg00XXk30FTf0R0#1#1#1#1#1#1#1#1p=j%10#0p=8%00#9p>01%20#2#2p=q%20#2p>0?%20#2#2#2p=V%20#2#2#2#2#2#2#2p=v%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=\%90#:p=Bg00Y5R1f1R2<070p=Zg00YaS00g00ZAS01P2P0C|p>0;g00[3R3?420p=lg00\ER4f2R5P2P0Cep=H%10#0#0p=?%10#1#1p=p%00#1p=6%10#1p=G%00#0#0#9p=5%10#1#1#1p=X%00#0p=7%:0:0712p=[%00#0#0#1p=L%00#Ap>06%00#0#0#0p=F%00#0#9#:p=WAw120p=_g00\cR6%C2;40p>0>%C5%C2=460546p=Ef3R7%C2=4609465546p=nf4R8A462094659467546p=T%C7A46209465546p>0=%00#0#0p==1J75?m20p=M%00#0#0#0#9p=S%05#A,J7?m20p=I%10#1#0#0p=u%10#0#1#1p=h%10#0#0#0p=D%00#0#1#1p>03%00#1#0#0p>0N%10#9p=s%:09m52p>0D%00#0#1#1#0#0#1#1p=r%00#0#1#0p=f%00#0#0#0#0#0#0#0p=O%A0,J2p>0L%92/Q0p>09%90,Q2p>0Kg00^1R9A4920745p=N1Q52=490p=~1J87?m52=490p=>%08#9/Q7%05#9/Q2=490549p=k%05#9/Q2=490p>0J1Q871Q52=490549p>0IA4920949594979498p=@%A7,J8?m52=490p=3%07#A,J8?m52=490p=KP4P4P2P0Cep=cP5P4P2P0Cep=dP7P6P6P6P5P2CeP0Cep=RP5P6P2P0Cep=tA4920p>0Gf6R:f5R;P8P7P5P2P0H05H05p=oP8P71U52P0H05p=Yg00_AR<?]20p=bB0F<20p=`A;:;8A;752/<0'<p=P&0O3R0,i4R7g00`TR5#0R2#1R;#0R:#0S02#0S03#0R8#0R=#1#j#8$01R>g00a9S04%A5#:S05g00aeR?#2R@#2RA#2RB#2RC#2S06#qRD$0?#V#v#\S07#q#v#\#\#\#\RE#CRF40E%15RG#1RH#1RI#1S08#1RJ#BRK'Z%95S09#:R5+0;&0:3R3'l5H0RL;;Lg00bDRM$0HRN%1;S0:#?S0;#8S0<#0S0=#pRO#6#GS0>#5RP%92RQ%18S0?#GRR#?#X#5RS%C?RT%02R2#0RU#1RV#1S0@#0S0A#7S0B#0RW#ARX'[RY1ZTF%0URZ#1R[#1R\#1R]#G#A#:R^'ZS0CPY%B8R_%12R2#0R`#1Ra#0Rb#GRc#?#LRd#0#BReP5&06WRW,[TRf&0?E#V#\#\#\RE#2#VS0D#2S0E#2S0F#VS0G#2S0H#2S0I#2S0J#2S0K#2S0L#2S0M#q#vS0N#2S0O#2S0P#2S0Q#2Rg%:SS0RPf%0[R[#7S0S#7Rh#F#WS0T%0GRG#0S0U#1Ri#0S0V#1S0W#1#FS0X#0S0Y#8S0Z#7#5S0[#:S0\%2g#VRj%2jRj%2jRj%BaS0]%1JRk#1#jS0^#1Rl#1#XS0_#1#jRm#BRnP5%VjRj#C%2jRj%2jRj%2jRj%2jRj%2jRj%2jRjg00cZS0`g00dFRo#:Rp1_FpRq'_S0a%BVS0b'_Rr7wnS0cPr%:PRs%1d#BS0dP5PePp1_qpS0eP5Pq%qj#vRj%2jRj%2jRj%2jS0f&0:6Rj+0>3ECnDTDT3E3E3EDT3ECnH0=Pp%1ORO#0Rd#1S0g#1#5S0hPD%=IS0i#0S0j$06,[TS0kCMS0lPp%1ORO#0S0m#SPDPYCMS0nPp%1OS0o#SS0pPDPYCMS0qPT%0VRV#1RO#1S0r#7PDPpCIS0sPT%0VRV#0S0t#0S0u#0RIPDQ0aCIS0vPT%=OROPDPFCIS0wPTPWPD%0ZRW#1Rt#7Ru#u#h#BCMS0xPT%?VPDPpCIS0y%9l9gFoS0zPT%=JPD%CARJCIS0{PT%0`R`#0Rl#0S0|#0S0}#0S0~#ARVPD%1:Rv#0Rw#7Rx#AS10,[TCMS11PT%AIP@%BWRICMRyPT%AOPD%1GRG#1RO#?#uRz#1#6#6#u#L#h#u#D#L#G#6#L#8#X#6#h#8#BCMR{1JTXS12%7z#h#L#8#6#F#L#G#6$03$0N#h#6#8$03#L#s80DDS13PT%7]PD%pmRm$03#r#r#r#6#BCIS14PT%=\PD%1m#X#jRm#0#j#j#BCIS15PT%7kPD%?iRi#G#r#r#WCIS16PT%0uPD%7bRb#8#f#6#BCIS17PT%DvS18PDQ00PAPoPDH0MRvPT%0WRW#7S19#7Ru#APD%0HRH#1S1:#0Rk#GR\#0S1;#0R]#1Rz#6S1<#6RX#1R|#SR}#:R~CMS1=PT%?WPDPpCIS1>PT%?tPD1[TVRVCIS1?PT%?[PDQ0kCIS0kPT%AhPD%12R2#1Rh#=R[#ARt,[TCMS1@PT%?wPDPpCIPT%7xPDPpPTQ02#1Rx#DPDPpPT%FxPDPpPTQ03#8S03#7PDPpPT%7=PDPpPT%DhPD%B;R;PTP[PD%D\#f#8#WS02PT%02R2#1R\#=PDP5PT%72R2#0R[PDP~PT%DaPD%6c#8#X#BPTPbPDPsPT%1`S1A#=S1BPD%fRS1C#f#WPp%0dRd#1#5PDPpPp%SdS1DPDPpPpQ0<#8Rd#7RR#DR`#5S0<PC%1m#XRm#p#j#sRc#:Pp%0RRR#6Ra#1#5PDP_Pp%SaS1EPDPYPpPPPCP;PTQ0}PDPpPTPbPDPpPTP[PDPpPTPtPDPpPTQ0BPDPpPTQ0@#1S0@#=S0BPDQ0:#=S0:$06Rt,[TR[PTQ0uPDPvPTQ0SPDPpPTQ19PDPpPTQ08#=PD1ZTIS08PTQ0jPDPJPT%7kPD%:QRkPT%7HRH#0S0jPDP~PT%=OPDQ0?#7#D#f#WPT%=GRGPDP[PTQ0V#7PDPvPTP2PDPpPTP=PDPpPTQ10PDQ07#CR2PTPtPDPJPTQ0tPD%BHPTQ0|PDPpPTQ0U#0Rt#7S0UPDPkPTQ0;PD%1GRv#G#8#8#8#WPpQ0W#0#XR[#1RO#0RI#0#GRb#8$01PCQ0`1_2p7wpQ0^#F#O#O#O#5R;%7uRu#FRa#=#FRh#0Rx#D#O#O#5Rw5gJ%=m#O#s=g2cPTQ0iPDPpPTQ0jPDPpPTPGPDPpPTQ0UPDPpPTQ0:PDQ08PTP8PD%6v#6#L#WPTPlPDPkPTPWPD%9URU#:RW,ZTPTPHPD%1\R\#6#G#8#h#W%9ZRZ-0<T%Fx#O#O#59gT;20LThRx%9hRh+0CPTPoPDPkCMPTPUPD%C@PTPZPDPJPT%9tPDPp%CBRt?g;w%CCRk?g;wPxPh1Jto%9=H0BPxPh1JkoPZH0B20<tU20<kUQ0=#=#F#5,Jp%=i#F#5+0C209aPQ0>#8Q1DQ0g#=Q0hQ0m#?Q0pQ0o#?Q1E%1R#FQ0<%8`%Gd#8#FRd$01%sd%6[#GR[#S%7]R]#6Rd#0#6#5%1d#6#5Pp%1[#5R[PD%:[Pp%5bPCQ06#CRb%1I#f%pORO#S%?OQ0Y#0RO#6RI#SR[PpP[PD%8zRz#0R[#7Rd#1#5R`#:%?I%1O#8#5RO1JpO@08WAQ0[Q0Z#1RO#F+0K%?OQ0X#1#8#6#5%?]#F%6X#5RX1Jp}@08WA%D|Q1<#1R|#0RA#7#5+09%1ARA#=#s%1A#5RAPpPAPDPt%1|R|#0Rt#=%1t#5%u|%SdRdPpPdPD%9uRu#:%p[#5R[1Jp[@08WB%?z#FQ1;#8#f#6#5Rz+09Q1:#D#O#5Q09Q0_#95gb1Qou&0:93N5~z3N5~`D>DkD>3~3N9~X}Dk3N40JD>DkD>D>I0IDkDkDkD@D@D>D>D>D@D3D3D3D3D3D3D3D3D33ND>DKDKD3D3D>D>D3D3D3DKD3DKD3D3D3D3D3D3D3D3D>D3D3D3D>D>D>D>D>D>RXD3DKD3DKD3DKD3D3D3D3D3D33ND@DK3ND@D@D@D@R}M<},^MR`;;`Rz1i44R9/i4R41cSP=d9QRS;;SRu1i66Ro/i6Rb/i6RWPoPYQ0CPeCR=tb5RB;;BR[AH0>3Rd=;7dR|PPPQQ1C#1#6#5RtPYPYPYP_PpPpPVQ0f#2RA%:tPVQ0TQ0\%2A#VR]%2]R]%2]R]Ps1_5rPp%V]R]#C%2]R]%2]R]%2]R]%2]R]%2]R]%2]R]P~P5Q02PpPpPpPpPpPpPp%q]#vR]%2]R]%2]R]%2]00>j3ECnDTDT3E3E3EDT3ECnH0=R]Q0lQ0nQ0qQ0sQ0vQ0wQ0xQ0yQ0zQ0{Q11PyQ13Q14Q15Q16Q17Q1=Q1>Q1?Q0kQ1@00GXD@D@RX5N{D@D@D@M<},^MR~=;N~RO1ctP=d9QRI=;4IRRPoPYPYPpCRRa=;baRi%1\#h#X#5=H03R\=;7\Rk20;KFg00ddRUg00eDRZPUP?PCPFH0AQ0eC|/l3'l9H0>Rh=;7hRxPPPQQ03#1#L$03#5R=PY1ZT^RwPYP_PJPFPfPE%:=PfQ0TQ0\Q0DQ0EQ0FQ0]PnPFQ0G#CQ0HQ0IQ0JQ0KQ0LQ0MPpQ0bPsPePpPJPpQ0eQ0aPqQ0NQ0OQ0PQ0Q00>j3ECnDTDT3E3E3EDT3ECnH0=P}M<},^MR}=;N}Rj1c=P=d9QR==;4=RqPoPYPwPJCRRJ=tbFRF=;WFRwQ18#8#6#L#8$01=H03Rf=;7fR;PPPQPtPYQ0r#G#A,[TRtPYP_PpPpPVP]Q0lQ0nQ0qQ12%9:80D@PTQ1A#DPDQ0dPTQ1BPDPsPT%DlPDPrPTQ0~PDQ0cPTQ0@#DPDPnPTQ0BPDQ0]PTQ0A#DPDQ0RQ0sQ0vQ0wQ0xQ0yQ0zQ0{Q11ANy{XD@D@D3DKD3DKD3DKD3D@M<},^MRX=;NXR{PoPYPtPpCRRt=;btRy/<kRD,<RRn'<Rr,<|Rl'<Rs'<R@'<R:'<R]'<RV'<R_'<RQ'<RP'<RH'<Rv'<R8'<RG'<P7PLPzPGPNP`PuP8P4PSP[PvPWPBP|PH1U7dRHPOPP1UN~PRPQ1U4IRQPiP_1UbaPkPV1U7\RVPxP]1U7hPjP:PNP}PqP@P4P=PwPsPWPFP;PlP7PfP|PrPHP{Pn1UNXPRPDPQPyPk1UbtPVFoFoDYDYDYDYFoFoFoDYDYDYDYP71i<0R<g00f6RVg00gG3]Rk,b0#a1`0k5H0Q04Q05g00hVRk40E/ZK00;5/l39H0>PNg00idg00k45zgg00lDRg,^MP4%yg&04g'c&00g5d9PSPWPo%xg&02g&0@gCR%{g5tbPoPYB071Tk/Z^PeCR=tb5P7g00mT9]<VR5,b0#a1`055H0PdPNg00ncg01035zAg011CR5,^MP4%y5&045'c&0055d9PIPbPo%x5&025%{5CRPaP7g012S9]<VRa,b0#a1`0a5H0P\P7g013b9]<VRa,b0#a1`0a5H0Q00Q01PKPkC|PUPZPUP?PCPkH0AAw1kp/_pC|/l3'l9H0>PNg0151g016A5zEg017QRE,^MP4%yE&04E'c&00E5d9P=PWPo%xE&02E&0@ECR%{E5tbPbP6PJPkCeP7g018a9]<VRk,b0#a1`0k5H0PfP7g01:09]<VRf,b0#a1`0f5H0PdPNg01;?g01<O5zAg01=_RA,^MP4%yA&04A'c&00A5d9PIPbPo%xA&02A%{ACRPtg01>o9]<VRV,b0#a1`0V5H0=;7\FPFPFPFPFPFPFPFPFPdo"). Qed.

Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xad434%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0xac48c%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xac48c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xacf80%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xac48c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xac48c%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xac48c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xa0ffc%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x9bdf8%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0OpenFail_defs ()) ["FPX_1"] "p%0p&0p;1p;2p;3p;4p;<g0000k10JTg000Pj2cTg0010j10Tg001Uj11Tg007?j1qTg007_j3=Tg003fj12Tg004Ej1ETg002Xj16Tg00Flj4VTg00;9j2@Tg01@>j4zTg00E^j4yTg002:j1MTg005Sk305Tg006aj18Tg0089k10ITg008[j3mTg009ij3ZTg00<Hk40HTg00=Vj2vTg00>fk201Tg00@6j4~Tg00AFj3tTg00BVj2NTg00Cfm<0CTg00E<j2}Tg00Umj4FTg00H>j2ATg00HYj2|Tg00I3j3ITg00T_j3rTg00J\k30BTg00L1k10ATg00MBk10@Tg00NQk10=Tg00Oak10<Tg00Q1k10;Tg00SPk10:Tg00VMj3;Tg00Vmj3\Tg00X=k406Tg00IPj1{Tg00XXk300Tf0R0#1#0p=>%10#0#0#0p=Y%00#1p=4%10#0#1#0p=`%00#8p=eg00\ER1f2R2f1R3P0CFp=C%00#1#0#0p=o%00#1#1#0p=[%20#2p=i%20#2#2#2p=n%20#2#2#2#2#2#2#2p=x%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>03g00Y5R4?m30p=W%10#1#1#1#1#1#1#1p=]%10#1#1#1p=S%10#1#1p=^%00#0#0p=<%00#0#0#0#0#0#0#0p=P%10#8p=lg00[3R5?;30p=G%00#0#0#0p=:%00#0#0#8p=5%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=dAr430p=B%80#6p=Kg00ddR6g00ZAS00P3P0CVp=p%10#1#1#0p=j%10#0#0p=J%10#1p=?%00#0p=9%00#Mp=b%00#0#8#6p=U%00#0#0#0#8p=Rg00\cR7%E2%E3=;703;p=aA;7309;72p=Q%E3=;70p>04%00#0#1#1p=h%00#0#1#0p=Xf3R8/@2?\30p>02%10#1#0#0p=w%00#0#1#1#0#0#1#1p=g%M0,@3p>0G%83/N0p=u%80,N3p>0Fg00^1R9A;9307;2p=D1N23=;90p=kf4R:/@8?\23=;90p=7%0:#8/N8%02#8/N3=;905;9p=_%02#8/N3=;90p>0E1N:81N23=;905;9p>0D%M8,@:?\23=;90p=3%08#M,@:?\23=;90p=L%M8,@:%83#67\2=;90p=f%18#0#0#0#M,@:?\23=;90p=OP7P7P3P0CFp=sP:P81|23P0H06p=Hg00_AR;?I30#{p>09B00;30p>08P1P8P2P3CF==:0p>07A=823/A0p>0>f6R<f5R=;=:A=823/A0'Ap>0?f7P1P<AI;=:#{B00;82CF;=3/A0p=T&0J5R0,c1R3g00`TR8#0R2#1R=#0R:#1R<#>R>#>#Y#4#`#e%q5R55C0R?;=?%0>R>#0#>#o#[#eR@g00YaRAg01APg00aeRB#2RC#2RD#2RE#2RF#2S01#2#iRG#i#n#x$03RH#ERIg00dFRJ#6RK'WS02%18RL#1RM#1RN#1S03#1RO#1RP#1#]S04#1RQ#1#SS05#1#]RR#^RS#1#S#]RT#1#SRU#<#P#lS06#6CV/G55C0RV==3VS07AC0@5RW==3WS08%1>#S#:#5=C05R>==3>S09PAg01BBS0:%2H#i#x#d#dRH#ERX/WKRYPXCV%EDRZ/BX/@JPCPAPKCz/G5'G9C0@R[==3[S0;%KOR\/pXP6g00eDS0<P6PBPFPXCy1WYKCV/G5'G9C0@R]==3]S0=g00a9S0>%M8#6S0?<05X/B\%88S0@#6R8'p/G59C0@R^==3^S0A%<:R:#0R_#^#S#j#e=C05R`==3`S0Bg00bDRa$0IS0C%1=Rb#JS0D#>Rc#0S0E#^Rd#4#?S0F#5Re%82Rf%1:Rg#?Rh#0#4#4#4#5Ri%EBRj%02R2#0Rk#1Rl#1Rm#0S0G#9S0H#0S0I#MS0J#6'BRn1BjX%0kRo#1Rp#1Rq#1Rr#1#b#6S0K'BS0LPn%K:S0MPKPK%12R2#0Rs#0Rt#0S0N#0S0O#0S0P#0S0Q#MS0R#6,BjRu%iH#n$03#d#d#dRH%6i%0pS0S#9S0T#9S0U#:#U%0LRL#0Rp#1Rv#0Rw#1Rx#1#:S0V#0S0W#>S0X#9#5S0Y#6%2H#nRy%2yRy%2yRy%6eS0Z1WKYS0[%Kl'WRY,W8%nyRy#E%2yRy%2yRy%2yRy%2yRy%2yRy%2yRy%0MRM#1S0\#0Rz#?R{#0S0]#0S0^#1S0_#4S0`#4S0a#1S0b#RR|#6R}%>{#:#`#U%2y#i#xRy%2yRy%2yRy%2y%q73a3a9QKK9QKK9QKK7QK7Q83a3a3a5QK3Q+043a3Q7Qu+04PK%1dRd#0Ry#1R{#1#5S0cPG%<NS0d#0S0e#b#6,BjS0fPK%1dRd#0RN#RPGPnPK%1dRd#RS0gPGPnPj%1tRtPG%1sRs#0R~#?#Y#h#KPj%:tPGQ0ZPjQ0NPGPYPjQ0QPGg00cZRt%KRRR;mYPj%1mRmPGPRPj%<mS0QPG%KsPjQ0GPG%>h#4#j#UPj%0lRl#1RhPGPKPj%0lRl#0S0G#0S0Z#0RsPGQ0[Pj%<hRhPGPXPjQ0IPG%0oRm#1RR#9RY#?#X#?#KPjPlPGPK%8Q9ZXJPj%<O#bPGPZH02PjQ0RPG%9<#bR<#6,BjPjPsPC%KmRsPjPhPG%1LRL#1Rh#J#wRO#1#4#4#?#:#[#S#X#:#4#?#o#[#S#[#jPjQ0JPG%0O#4#[#h#X#:#h#`#4#`#4#[#w#[#h#KPj%<rPG%hS#g#g#g#4Pj%:qPG%0T#]#]Pj%<PPG%JvRv#?#g#g#UPj%9YPG%9~R~#>#X#4Pj%0mRm#9RY#9RPPGP}PjPmPGPKPjPRPGPuPjQ0SPGQ0fPjQ0UPG%12R2#J#bRu#6,BjPK%0yRy#1#5PGPKPK%RyRyPGPKPK%>cRc#9RR#YRT#5RqPF%^U#]#lRU#6PK%0RRR#4RS#1#5PGQ0MPK%RSRSPGPnPKPePF%K=PjQ0PPGPKPjP~PGPKPj%02R2#9R~PGPKPjPuPGPKPjQ0HPGPKPjQ0QPG%<bRb#bRu#6,BjR=PjQ0ZPGPAPDPJPGH0HRrPjQ0TPGPKPjPYPGPKPjQ03#<PG1BjsRsPjQ0ePGPZPj%9zPG%6fRzPj%9MRM#0RYPGP}Pj%<hPG%9g#Y#X#UPj%<LRLPGP=Pj%9wPGPrPjP~PGPKPjP_PGPKPjP<PGPIPjPuPGPZPjQ0GPGPMPjQ0OPGPKPj%0pRp#9RuPGPzPjQ0DPG%1LR<#j#`#UPK%0x#SRx#1R~#0Rr#0#?Rw#>#ePFQ029mtKQ04#:#P#P#P#5Rt%9PRP#:R=#<#:Rg#0Rh#Y#P#P#5R}5ZZQ06=ZIUPjQ0dPGPKPjPYPGPKPjPLPGPKPjPuPGPKPjPbPGPsPjP:PG%4<#o#4#UPjQ0NPGPzPjPmPG%8kRk#6Rm,BjPjPMPG%?2R2#4#?#`#?#U%8oRo,vj%:h#P#P#59Zjt20GjgRh%8gRg+01PjPJPGPzH02PjPkPG%ECPjPoPGPZPj%8pPGPK%EERp?Zt}%EFRz?Zt}PhPg1@pJ%8_C~PhPg1@zJPoC~1vpk1vzkQ0E#<#:#5,@K%<v#:#5+011u=eQ0F#>Py%<{Q0c%JNQ0g%JdPS%1R#:Pq%>T%jc#:Rc#e%lc%4x#?Rx#RQ0^#9Rc#4RT#0#4#5%1T#4#5PK%1x#5RxPG%6xPK%5wPFQ01#ERw%1r#X%^~R~#R%J~Q0W#0R~#4Rr#RRxPKPxPGQ0_#>Rx#0RT#9Rq#1#5RR#6%Jr%1~#>#5R~1@K~?tmDQ0YQ0X#1R~#:+0F%J~Q0V#1#>#4#5%Jc#:Q0a#4#5Rc1@K|?tmDQ0b#YQ0`#1RD#0R~#9#5'u%1~R~#<#l%1~#5R~PKP~PGPp%1DRD#0Rp#<%1p#5%wD%RqRqPKPqPG%8PRP#6%^T#5RT1@KT?tmE%Jx#:Q0]#>#X#4#5Rx'uQ0\#Y#P#5Q0@Q05#85Zw1NJP%q93D5kx3D5kRD7D_D73k3D9kc|D_3D40ED7D_D7D7I0DD_D_D_3D3D3D3DD7D7D73D3DD3D3D3D3D3D3D3D3D33DD7DLDLD3DfD7D7D3D3D3DLD3DLD3D3D3D3D3D3D3D3D7DLD3D3D7D7D7D7D7D7D3DODODOD3DfD3DfDfD7DfD3D73DDODLDLDLDODODLDODLDOD3DOD7D7D7N<0C,}aRc;=cR|1c11RR/c1RxPRP1P1P1PiPeCFPfCFRf;=fRe1c77Ri/c7R9PiP7Q0L,snPKCFRP;=PRw%12#>#?#S#5=C05R2==32Rm'ARE'ART'ARG'ARq'ARD'ARp'AR~'ARr'ARS'AP3P?Q07PSP3PVQ08PrP3PWQ09P~P3P>Q0;PpP3P[Q0=PDP3P]Q0APqP3P^Q0BPGP3P`P|PTQ0CPcPePEPxPfPwPmP9PP1|32DHDHDHDHDHDHDHDHDHDHDHP3P0P01c;0R;g00f6RPg01C43IRmP0PmP?P3P0P0g01DB9I;PR?P0P?PVP3P0P0g01EP9I;PRVP0PVPWP3P0P0g01F^9I;PRWP0PWP>P3P0P0g01Gl9I;PR>P0P>PAQ0:g00hVR>=m4KRWP>CVAr4Z>/@JPCPAPKCz/G5'G9C0@P3P0P0g01I:9I;PRAP0PAP6Q00P\P>CVP6Q0<P6PBPFP>Cy1WWKCV/G5'G9C0@P3P0P0g01JH9I;PRWP0PWQ0>Q0?<05>/B\/p8/G59C0@P3P0P0g01KV9I;PR@P0P@P`Q0Cg01Ldg01N360BHg01OBRH,}aPxPRP1P1P1&0AH&0@HCF&0=HCFPfP9PiP7&0<H&0;H's&0:HCFPiP7Ar4j>Q0K'B,snPKCFP3P0g01PR9I;PRP-0902080PP2I07H0>K0?GTGTGTGTGTGTGTGTdo"). Qed.

End FPX_1.
