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
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Es0MainEntry SymDriveH4
  Es0LibStdioCall Es0OpenFail_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Es0MainEntryN.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_lC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_sC13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~K47Corelib4Init9Datatypes4bool02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs2LXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_srGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_knGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_scGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs4u_rHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_srF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_knF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_scF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_srG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_knG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_scG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_srE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_knE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_scE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_srG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_knG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs6u_scG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Es0Usage_defs5u_rH4C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x34544 sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0xa17d8 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0xa17d8 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0xa2348 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0xa17d8 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0xa17d8 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0xa17d8 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0xa1ca8 u_srH0 [] u_knH0 262.
Definition u_rH := Eval vm_compute in run scr0 u_ssH0.
Definition u_srH : list expr := Eval vm_compute in s_regs (fst (fst u_rH)).
Definition u_knH : list kentry := Eval vm_compute in kn_after u_rH u_knH0.

(* [comment removed for export] *)
Definition u_scrF3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition u_rF3 := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 : stdio_res := Eval vm_compute in sc_of 198 u_srF3 u_knF3.
Definition u_srG30 : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 230.
Definition u_rG3 := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 : stdio_res := Eval vm_compute in sc_of 230 u_srG3 u_knG3.
Definition u_srH30 : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 : sym_state := SS 0xa1ca8 u_srH30 [] u_knH30 262.
Definition u_rH3 := Eval vm_compute in run scr0 u_ssH30.
Definition u_srH3 : list expr := Eval vm_compute in s_regs (fst (fst u_rH3)).
Definition u_knH3 : list kentry := Eval vm_compute in kn_after u_rH3 u_knH30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition u_rE4 := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 : stdio_res := Eval vm_compute in sc_of 166 u_srE4 u_knE4.
Definition u_srF40 : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 198.
Definition u_rF4 := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG40 : sym_state := SS 0xa17d8 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0xa1ca8 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0xac48c%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0xac48c%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0xacf80%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0xac48c%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0xac48c%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0xac48c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0xa0ffc%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x9bdf8%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0xa0ffc%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0xa1e78%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x110ba, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0xa0ffc%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x9bdf8%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0xa0ffc%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0xa2898%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0xac48c%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0xa0ffc%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x9bdf8%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0Usage_defs ()) ["FPX_1"] "p%0p%1p&0p;1p;2p;4p;3p;<g0000k10VTg000Pj2bTg0010j10Tg001Uj11Tg002:j12Tg002Yj1:Tg003gj1?Tg004Ej18Tg005Sj4VTg006ek10?Tg007Ej37Tg007_j2GTg008nk40GTg00:@k40FTg00;Nj1ETg00;lk30ETg00=:k10NTg00=\k30>Tg00>jk303Tg00@:k40UTg00AHk20TTg00BXk20JTg00Chk30:Tg00E8j2eTg00FHl<wTg00G^j2PTg00H@j24Tg00H[j2iTg00I5j3>Tg00IRk306Tg00J`j3sTg00L5j1zTg00MFj1yTg00NUj1rTg00Oej1qTg00Q5j1pTg00REj1uTg00STk10DTg00Tcj4ITg00UCj36Tg00Ucj3cTg00W3j4vTg00WNk30CTg00Wkk105Tf0R0#1#0#0p=K%10#0p=A%00#1#0#0p>0;%00#1p=;%00#?p=~%20#2p>08%20#2#2p=k%20#2#2#2p=Ug00Y7R1f3R2f2R3g00YUR4f1R5;60CIp=NP1P3P5P0CIp>01%10#1#1#1p=f%00#0#0#0p==%00#0#0#?p=5%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=[g00ZgR6@0>50p=jB06650p=@A6450p=|%?0#8p=Fg00[SR7g00\3R8P5P0CVp>07%10#1#1#1#1#1#1#1p=_%10#1#1p=o%10#1p=T%00#0#1#0p=h%00#0p=9%00#Ep>04%20#2#2#2#2#2#2#2p>0B%00#0#?#8p=a%00#0#0#0#?p=Y%10#0#1#0p=ng00\eR9%:5;60p>0A%:3%:5=690569p=C%:5=69096939692p=mf4R:A695096939692569p=X%:2A69509693569p>0@%00#0#0p=<1G23?c50p=`%13#0#0#0#E,G2?c50p=L%03#E,G2?c50p=W%10#1#0#0p>0=%10#0#1#1p=g%00#0#1#1p>02%10#0#0#1p=l%10#?p>0<%809c35p>0K%00#0#1#1#0#0#1#1p=x%10#0#0#0p=J%00#0#0#0#0#0#0#0p=]%E0,G5p>0S%?0,e5p>0R%?5/e0p>0Ig00^3R;A6;50763p=S1e35=6;0p>001G:2?c35=6;0p=D%03#?/e5=6;0p=H1e:21e35=6;056;p>0HA6;5096;396;296;:p=B%E2,G:?c35=6;0p=3%02#E,G:?c35=6;0p=\A6;50p=}P2P1P1P1P3P5CIP0CIp=ZP2P9P9P9P3P5CIP0CIp=Og00_CR<P8P5P0CVp>09P3P9P5P0CIp=dP9P9P5P0CIp>0Qf7R=f6R>f5R?P:P21i35P0CvCvp=^P:P21i35P0Cvp=MP>P?P:P2P3P5P0CvCvp>0Pg00_cR@@0C50p=tP1P2A>@35$05P0CIp={A>@50$05p>0OP1P2P3P5CI=7:0p>0MA7235/40p>0LA7>?:A7235/40'4p=RP1P>A>@?:$05B0C@23CI=7=5/40p=Q&0V4R0,b1R=P0g00a6R5#0R3#1R2#0R?#1S00#KR:#0S01#A$0;#;#A#~R>P7g00a[g00bMRA#2RB#2RC#2RD#2RE#2S02$08RF#2RG#k#US03#2RH#:%?3RI#8S04CV&0?4R4CNRJ;7JB010>4RK=7=KRL%1:#f#=#5>0104R:=7=:S05P0P>P<g00blS06%kHS07#2S08#2S09#2S0:#2S0;$08S0<#k#U#[#[#[#[#[RH#:RMg00c^RN#8RO'jRPPMCV%:BRQ/@M/GNPBP<POH0G/|4CNRR=7=RS0=P0P>%03R3#1S0>#0S0?#0RS#1RT#FRU007MP7g00d<S0@P7PAPEPMH0F1jPOS0ACV/|4S0BCNRV=7=VS0CP0P>g00dnS0D%E5#8S0E<0EM/@US0F%15RW#1RX#FRY+07P4CNRZ=7=ZS0G%0?S0H#0S0I#0R?#0R[#1#_#A#~R\>0104R]=7=]R^g00eZR_$0NR`%12S0J#KS0K#AS0L#0S0M#oRa#;#TS0N#5RbPI%1?S0O#TRc#hS0P#1#;#5Rd%:ARe%03R3#1Rf#1Rg#0S0Q#9S0R#0Rh#ERi#8'@Rj1@eMS0S%0fRf#0S0T#0Rk#1$04#8S0U'@S0VPj%F?RlPOPO%0SS0W#0S0X#0S0Y#0RS#ES0Z#8,@eRm&08H#U#[#[#[RH#2#US0[#2S0\#2S0]#US0^#2S0_#2S0`#2S0a#2S0b#2S0c#2S0d#k$0BS0e#2S0f#2S0g#2S0h#2Rn#2#US0i#2S0j#2S0k#US0l#2S0m#2S0n#2S0o#2S0p#2S0q#2S0r#k$0BS0s#2S0t#2S0u#2S0v#2Ro%8dPm%03Rp#1Rq#0S0w#9S0x#9Rr#=#aS0y%0WS0z#0S0{#1RW#0S0|#1S0}#1#=S0~#0S10#AS11#9#5S12#8S13%2o#URs%2sRs%2sRs%8bRt1jOPS14/jYRu,jYPO%UsRs#:%2sRs%2sRs%2sRs%2sRs%2sRs%2sRs%0XS15#1S16#0S17#TRv#0S18#0S19#1S1:#;S1;#;S1<#1S1=#YRw#8Rx%?5S1>#8S1?%Av#=#n#aS1@POPOPOPOPOPOPO%ks$0BRs%2sRs%2sRs%2s&0?9Rs+0A3CCmDXDX3C3C3CDX3CCmH0@S1APO%1aRa#0Rv#1S1B#1#5S1CPG%1XRX#<S1D#0S1E$04#8,@eS1FC`R5PO%1aRa#0S1G#YPGPjC`RyPO%1aS1H#YS1IPGPjC`RaPePTPG%0kRz#1S1J#1#=#;#FS1KCLS1LPe%<TS1MPGPtCWS1NPeQ0WPGPuCLS1OPePSPGg00g0%1XRX#1RS#1RT#1#_R{#1R|#1#fS1P#1#_R}#FR~<0>uS1QCWS1RPe%1gRgPGP~CLS1SPe%<gS1TPGQ0?#1Rg#FS0?CWS1UPeQ0QPG%Kc#f#5S0Q#8S1VCLS1WPe%1fRfPGPOCLS1XPe%0zPGQ14CWS1YPe%9fS1Z#0PGPMCWS1[Pe&04hS1\PG%0pRh#1S1]#9Rf$0=#g#FC`S1^PeQ0TPGPOCLS0T%?|:03MNR|Pe%<SPGPQCWRSPeQ0ZPGQ00#0S00#9S0Z#ES1_#8,@eC`Rc1GeiS1`%0hRh#0Ri#o#;$02#h#g$02#g#=#g#l#g#n$0<80KFS1aPe%1qRqPG%o}R}$02#x#x#x#;#FCLS1bPe%<qPG%1}#f#_R}#0#_#_#FCWS1cPe%9TPG%KWRW#T#x#x#aCWS1dPe%0fPG%<gS1e#J#l#FCWS1fPe%0iS1g#9Ri#EPGPxC`S1hPePhPGPOCLS1iPeQ1]PGPmCLS1]PeQ0wPGQ1FCLS1FPe%ErPGQ0>#1Rr#1S0>#<S0w#ES1j#8,@eC`S1kPO%0vRv#1#5PGPOPO%YvS1lPGPOPOQ0L#ARv#9Rf#JRT#5RqPE%1}#_#_#FPO%0fRf#;R}#1#5PGPlPO%Y}R}PGPjPOPbPE%F2S0LPeQ0YPGPOPeQ1ePGPOPe%0rRr#9S0Y#0S1mPGPOPeQ1jPGPOPeQ0RPGPOPeQ1TPGQ0J#<S0J$04S1T#8,@eS0RPePzPGP<PCPNPGH0US1jPeQ0xPGPOPeQ1gPGPOPe%<XPGQ0<#:S0<PeQ1EPGQ0z#1RX#<Rz#1R2#;$0;#;#aS0zPeQ17#9PGQ03#:S03PeQ15#9S15#0S17PGPxPe%JXPGQ0O#9#J#h#aPePzPGQ0RPeQ0|#9PGQ1jPeQ0YPGQ09#:PeP[PGQ08#:PeQ1_PGQ07#:PeQ1TPGPQPePkPGQ0;#:PeQ0XPGQ0:#:PeQ0{#<RkPGQ04PeQ0KPG%A2#f#A#aPeQ1DPGPOPeQ17PGPOPePzPGPOPePkPGPOPeQ0JPGQ0<PeP?PGQ0zPeQ0WPGQ03PePhPG%?3R3#8Rh,@ePeQ15PG%1rRr#1R?#;#T#A#g#a%?p-0Te%={#]#]#]#5R{%9iRi#=Rp#<#=Rk#0Rz#=#]#]#5603e20Sek%?k+0JPeP3PGPQC`%Jz#]#]#5:03Q{Q0M#<#=#5,GO%<W#=#5+0J%?pPbQ0N#A#~Q1lQ1B#<Q1CQ1G#KQ1IQ1H#K%1f#=%AT%Tv#A#=Rv#~&0<vQ0}#0#fRv#;#TRT#YQ19#9Rf#;Rp#0#;#5%1p#;#5PO%1T#5RTPG%8TPO%1vRv#0RT#0#T#5PEQ02#:Rp%1T#h%ovRv#Y%KvQ10#0Rv#;RT#YRWPOPWPGQ1:#ARW#0R{#9Rz#1#5R3#8%KT%1v#A#5Rv1GOv@0:hCQ12Q11#1Rv#=+0R%KvQ0~#1#l#5%Kf#=Q1<#;#5Rf1GOw@0:hCQ1=#JQ1;#1RC#0Rv#9#5+0I%1vRv#<$0<%1v#5RvPOPvPG%:D%1CRC#0Rv#<%1v#5&0=C%YzRzPOPzPG%?iRi#8%o{#5R{1GO{@0:hD%KW#=Q18#J#l#5RW+0IQ16#J#]#5Q1>Q1P#?603p1eNi&0?;3S600W3S6003DD3H3HDD4003S:00fw3H3H3S3HDD3H3HDDDDI0H3H7Hq7H}3H3HI0H3SDBD3D3D3D3D3D3D3D3D3D\D\D3D3DDDDD3D3D3D\D3D\D3D3D3D3D3D3D3D3DDD3D3D3DDDDDDDDDDDDR}'}DBDBRq'}DBDBRf3SDBDBM<w,P_Rw;7wS1C1b11R3/b1R1P3PdPbPICZRW;7WR;1b99Ri/b9RpPiPjQ0VPOCORh;7hS0V%1?#g#f#5>0104R?=7=?RDP0P\Q0F009YP4CNR{=7={S0FPbPIQ0QPjQ0SQ1Z#1#E#8Rz'@RCPjPlQ1J#0#TRv#n#FRTPYQ1\#8,@eRkPnQ1VPkQ0yQ13Q0iQ0jQ0kQ0?P~PYQ0l#:Q0mQ0nQ0oQ0pQ0qQ0rQ1QPuPtQ1KPYPTPOQ0APYPPQ0sQ0tQ0uQ0v00As3CCmDXDX3C3C3CDX3CCmH0@P5PyPaQ1XQ1YQ1[Q1^Q0TP|PSPcQ1aQ1bQ1cQ1dQ1fPeQ01PGQ1jQ1hQ1iQ1]Q1FQ1kPeQ00PGPOCLPeQ0Z#9PGPOPeQ0H#1Ru#JPGPOPe%0uRu#<PGPOPeQ0I#AR2#9PGPOPe%9[PGPOPeQ0>#JPGQ0LPeQ0wPGQ1@Pe%<rPGQ1?PeQ1mPGPxPe%JgPG%9v#;#FPeQ1ePGPtPeQ1MPGQ0P#h#aP}D3D\D3D\D3D\D3D3D3D3D3D33SDBD\DBDBDBDBR}M<w,P_RG=7`GS1kP3Q0QPbPICZRv=71vS0Q1bp9RgPiPjPCPTCO=dpYRC;7CS0PPbPIPdPjPjPjPlPOPOPmQ1A1}af9S5yM<w,P_Rf=7`fS1MPiPjPjPOCORx=7pxS1eP0P\209UMQ0BCNRr=7=rS0BPbPI%K2#;$02#5R2Pj1@ezR[PjPlPQPMPkPH%82PkQ0yQ13Q0[Q0\Q0]Q0?P~PMQ0^#:Q0_Q0`Q0aQ0bQ0cQ0dPOPYPtPTPOPQPOQ0AQ14PPQ0eQ0fQ0gQ0h00As3CCmDXDX3C3C3CDX3CCmH0@P}M<w,P_R}=7`}S0]P3P2PbPICZR2=712S0\20Qj[Rs=diQS0`=dpMRM=7gMS0_PbPIPdPjP[PjPlPOPOPmQ1AP5PyPaQ1`%Au#J#n#n#n#=#l$0=#l#h$0;#580KFQ1LQ1NQ1OQ1RQ1SQ1UQ1WQ1XQ1YQ1[Q1^Q0T1}cq9S|SDBDBDBDBM<w,P_RS=7`SS0TAdisORs=7psS1^/4DS1[,4;S1Y'4S1X,4^S1W,4LS1U'4S1S'4S1R'4S1O'4R|,4DRq'4Rc,4;RF'4Ru,4^Ra'4Ry'4R5'4Rm'4Rl'4R['4Rd'4RI'4Rb'4RP'4Rt'4R~'4Rk'4RX'4P=PJPLPX1i=KRXQ05PkP=P:Q0=P~P=PRQ0CPtP=PVQ0GPPP=PZP^Pb1i=]RbQ1CPIP`PwP;Pd1i1WRdQ0VP[PpPhPDPl1i=?RlQ0FPmP=P{Q1kP5P`PGQ0QPyP1PvQ0PPaPgPCP^PuPbQ1MPFP`PfP;PcPdQ1ePqPpPxPDP|PlQ0BQ1OP=PrQ0]Q1RP`P}Q0\Q1SP1P2Q0_Q1UPgPMPLQ1WPXP^Q1XPbQ0TQ1YP`PSP;Q1[PdQ1^PDPpPsPlG^DMK0PDMDMDMG^G^G^DMDMDMG^G^G^DMDMDMG^DMP=P0P01b@0R@g00g\Rlg00hm3>RDP0PDPJP=P0P0g00j:9>@lRJP0PJPKP=P0P0g00kG9>@lRJP0PJP:P=P0P0g00lT9>@lR:P0P:P0P>P<Q06g00maR:>0>6ORJP:CVB066Q:/GNPBP<POH0G/|4CNP=P0P0g00nl9>@lRBP0PBP0P>P7P8PUP:CVP7Q0@P7PAPEP:H0F1jJOCV/|4RJCNP=P0P0g01099>@lREP0PEP0P>Q0DQ0E<0E:/@UR>007YP4CNP=P0P0g011F9>@lREP0PEP]P`g012Sg013a5sog014oRE,P_P1P3%zE%yE%rECZPWPpPi%qE%pE%uECOPiPjB066e:ReQ0U'@POCOP=P0P0g016=9>@lRO1t0OC{P?P=P0P0g017J9>@lROP0POP0P\209>YP4CNP`g018Xg019g5sng01;6Rn,P_P1P3%zn%yn%rnCZPvPgPi%qn%pn&0DnCO%un5dpPiPj1@ezPTCO=dpYP=P0P0g01<E9>@lRY1t0YC{P]P`g01=Sg01>b5sog01@1RY,P_P1P3%zY%yY%rYCZPWPpPi%qY%pY%uYCOPxP=P0P0g01A@9>@lRx1t0xC{P?P=P0P0g01BN9>@lRxP0PxP0P\P<P8PUP:CVPJCNP`g01C\g01Dk5sHg01F:RH,P_P1P3%zH%yH%rHCZP2PgPi%qH%pH&0DHCO%uH5dpPpP9Q0`P:CIP=P0P0g01GI9>@lR:1t0:C{PKP=P0P0g01HW9>@lRKP0PKP]P`g01Ieg01K45sog01LCRo,P_P1P3%zo%yo%roCZPWPpPi%qo%po%uoCOPsP=P0g01MR9>@lRl-0O01t0lP?I0MH0LFRGQFRFRGQFRFRFRFRGQFRFRGQGQGQGQGQGQGQdo"). Qed.

End FPX_1.
