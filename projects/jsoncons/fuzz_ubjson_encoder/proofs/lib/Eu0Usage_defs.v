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
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Eu0MainEntry SymDriveH4
  Eu0LibStdioCall Eu0OpenFail_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eu0MainEntryN.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0Usage_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_lC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_sC13~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~K47Corelib4Init9Datatypes4bool02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~K47Corelib7Numbers7BinNums8positive03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs2LXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_srGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_knGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_scGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs4u_rHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_srF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_knF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_scF3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_srG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_knG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_scG3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rH3C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_srE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_knE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_scE4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rF4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_srG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_knG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs6u_scG4C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=Eu0Usage_defs5u_rH4C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x34a4c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0xa3354 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0xa3354 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0xa3ec4 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0xa3354 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0xa3354 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0xa3354 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0xa3824 u_srH0 [] u_knH0 262.
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
Definition u_ssH30 : sym_state := SS 0xa3824 u_srH30 [] u_knH30 262.
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
Definition u_ssG40 : sym_state := SS 0xa3354 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0xa3824 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0xae008%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0xae008%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0xaeafc%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0xae008%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0xae008%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0xae008%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0xa2b78%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x9d974%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0xa2b78%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0xa39f4%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x110ba, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0xa2b78%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x9d974%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0xa2b78%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0xa4414%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0xae008%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0xa2b78%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x9d974%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0Usage_defs ()) ["FPX_1"] "p%0p%1p&0p;1p;2p;4p;3p;<g0000k10VTg000Pj2fTg0010j10Tg001Uj11Tg002:j12Tg002Yj1:Tg003gj1;Tg004Ej18Tg005Sj4ZTg006ek10=Tg007Ej36Tg007_j2ETg008nk40ETg00:@k40DTg00;Nj1GTg00;lk30CTg00=:k10NTg00=\k30<Tg00>jk302Tg00@:k40UTg00AHk20TTg00BXk20HTg00Chk309Tg00E8j2cTg00FHl<xTg00G^j2NTg00H@j24Tg00H[j2kTg00I5j3>Tg00IRk305Tg00J`j3rTg00L5j1oTg00MFj1pTg00NUj1qTg00Oej1uTg00Q5j1tTg00REj1sTg00STk10BTg00Tcj4HTg00UCj37Tg00Ucj3hTg00W3j4wTg00WNk30ATg00Wkk104Tf0R0#1#0p=a%00#0#0p==%00#0#0#0p=B%00#1p=<%00#0#0#;p=5%20#2p>06%20#2#2p=m%20#2#2#2p=Ug00Y7R1f3R2f2R3g00YUR4f1R5;70CHp=MP1P3P5P0CHp>00%10#1#1#1p=e%10#0#0#;p=j%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=\g00ZgR6@0<50p=iB05650p=?A7450p={%;0#8p=Dg00[SR7g00\3R8P5P0CZp>07%10#1p=Q%10#1#0#0p=b%10#0#0p=P%00#0p=9%00#Gp=y%20#2#2#2#2#2#2#2p>0@%00#0#;#8p=`%10#0#0#1p=_%00#0#0#0#;p=Y%10#1#1#0p>03%10#0#1#0p=Xg00\eR9%:5;70p>0?%:3%:5=790579p=A%:5=79097939792p=nf4R:A795097939792579p=W%:2A79509793579p>0>1E23?h50p=^%13#0#0#0#G,E2?h50p=K%03#G,E2?h50p=V%10#1#1#1#1#1#1#1p=g%00#0#1#0p=l%10#1#1p>01%00#1#0#0p>0J%10#;p>0;%809h35p>0I%00#0#1#1p>0:%00#0#1#1#0#0#1#1p=~%10#0#0#0p=F%00#0#0#0#0#0#0#0p=J%G0,E5p>0S%00#;p>0R%;0,c5p>0Q%;5/c0p>0Gg00^3R;A7;50773p=S1c35=7;0p=}1E:2?h35=7;0p=C%03#;/c5=7;0p=I1c:21c35=7;057;p>0FA7;5097;397;297;:p=@%G2,E:?h35=7;0p=3A7;50p=|P2P1P1P1P3P5CHP0CHp=[P2P9P9P9P3P5CHP0CHp=Og00_CR<P8P5P0CZp>08P3P9P5P0CHp=dP9P9P5P0CHp>0Pf7R=f6R>f5R?P:P21k35P0CwCwp=]P:P21k35P0Cwp=LP>P?P:P2P3P5P0CwCwp>0Og00_cR@@0A50p=vP1P2A>@35$04P0CHp=zA>@50$04p>0MP1P2P3P5CH=6:0p>0LA6235/40p>0KA6>?:A6235/40'4p=TP1P>A>@?:$04B0A@23CH=6=5/40p=R&0V4R0,f1R=P0g00a6R5#0R3#1R2#0R?#1S00#1S01#aR:#=#B#<#5R>P7g00a[g00bMRA#2RB#2RC#2RD#2RE#2S02$06RF#2RG#m#US03#2RH#:%;3RI#8S04CZ&0=4R4CMRJ;6JB000>4RK=6=KRL%1:#<#<#e#j>0004R:=6=:S05P0P>P<g00blS06%mHS07#2S08#2S09#2S0:#2S0;$06S0<#m#U#\#\#\#\#\RH#:RMg00c^RN#8RO'iRPPMCZ%:BRQ/?M/ENPBP<POH0E/{4CMRR=6=RS0=P0P>%03R3#1S0>#0RS#0RT#1RU#DRV007MP7g00d<S0?P7PAPEPMH0D1iPOS0@CZ/{4S0ACMRW=6=WS0BP0P>g00dnS0C%G5#8S0D<0CM/?VS0E%15RX#1RY#DRZ+07P4CMR[=6=[S0F%0?S0G#0R?#1R\#0S0H#1S0I#<#a#e#5R]>0004R^=6=^R_g00eZR`$0NRa%12S0J#aS0K#1S0L#0S0M#eS0N#0Rb#<#QS0O#5RcPI%b\R\#=S0P#P#jRd%:ARe%03R3#1Rf#1Rg#0S0Q#9S0R#0Rh#GRi#8'?Rj1?eMS0S%0fRf#0S0T#0Rk#1#y#8S0U'?S0VPj%0?R?#DRlPOPO%0TS0W#0S0X#0S0Y#0RT#GS0Z#8,?eRm&06H#U#\#\#\RH#2#US0[#2S0\#2S0]#US0^#2S0_#2S0`#2S0a#2S0b#2S0c#2S0d#m$0@S0e#2S0f#2S0g#2S0h#2Rn#2#US0i#2S0j#2S0k#US0l#2S0m#2S0n#2S0o#2S0p#2S0q#2S0r#m$0@S0s#2S0t#2S0u#2S0v#2Ro%8dPm%03Rp#1Rq#0S0w#9S0x#9Rr#B#`S0y%0XS0z#0S0{#1S0|#_RX#<S0}#1S0~#1S10#aS11#9#5S12#8S13%2o#URs%2sRs%2sRs%8cRt1iOPS14/iZRu,iZPO%UsRs#:%2sRs%2sRs%2sRs%2sRs%2sRs%2sRs%0YS15#1S16#1S17#0Rv#<S18#1S19#1S1:#0S1;#0S1<#<S1=#1S1>#YRw#8Rx%;5S1?#8S1@%Pv$03#X#`S1APOPOPOPOPOPOPO%ms$0@Rs%2sRs%2sRs%2s&0=9Rs+0?3ACnDWDW3A3A3ADW3ACnH0>S1BPO%1bRb#0Rv#1S1C#1#5S1DPG%1YRY#=S1E#0S1F#y#8,?eS1GC^R5PO%1bRb#0S1H#YPGPjC^RyPO%1bS1I#YS1JPGPjC^RbPePUPG%0kRz#1S1K#1#B#<#DS1LCKS1MPe%=US1NPGPtCVS1OPeQ0WPGPuCKS1PPePTPGg00g0%1YRY#1RT#1RU#1#gR{#1R|#1#eS1Q#1#gR}#DR~<0<uS1RCVS1SPe%1gRgPGP~CKS1TPe%=gS1UPG%1SRS#DS1VCVS1WPeQ0QPG%Q\$03#jS0Q#8S1XCKS1YPe%1fRfPGPOCKS1ZPe%0zPGQ14CVS1[Pe%9fS1\#0PGPMCVS1]Pe%yhS1^PG%0pRh#1Rf#9R\#Q#l#Q#DC^S1_PeQ0TPGPOCKS0T%;|:02MNR|Pe%=TPGPQCVRTPeQ0ZPGQ00#0S00#9S0Z#GS1`#8,?eC^Rg1EeiS1a%0hRh#0Ri$01$0J#b#X#b$03#b#l#Q#_#a#Q#X$0;80IFS1bPe%1qRqPG&01}R}$0:#~#~#~#<#DCKS1cPe%=qPG%1}#e#gR}#0#g#g#DCVS1dPe%9UPG%PXRX#Q$0:#~#`CVS1ePe%0\PG%=SR\#F#_#DCVS1fPe%0iS1g#9Ri#GPGPxC^S1hPePhPGPOCKS1iPePfPGPmCKS1jPeQ0wPGQ1GCKS1GPe%GrPGQ0>#1Rr#1S0>#0Rf#9S0w#GS1k#8,?eC^S1lPO%0vRv#1#5PGPOPO%YvS1mPGPOPOQ0N#1Rv#FRU#5RqPE%1}#g#g#DPO%0vRv#<R}#1#5PGPlPO%Y}R}PGPjPOPcPE%D2S0NPeQ0YPGPOPeP\PGPOPe%0rS0Y#9S1n#0S1oPGPOPeQ1kPGPOPeQ0RPGPOPeQ1UPGQ0J#=S0J#yS1U#8,?eS0RPePzPGP<PCPNPGH0URzPeQ0xPGPOPeQ1gPGPOPe%=YPGQ0<#:S0<PeQ1FPGQ0z#1RY#9Rr#1R2#0#_$0:#`S0zPeQ16#=PGQ03#:S03PeQ15#9S15#0S16#0PGPxPe%FYPGQ0I#1#<#F#<#`Pe%0rS0I#0RrPGQ0RPeQ0|#=PGPzPeQ1nPGQ09#:Pe%0?RYPGQ08#:PeQ1`PGQ07#:PeQ1UPGPQPePkPGQ0;#:PeQ0XPGQ0:#:PeQ0{#=Rk#0PGQ04PeQ0K#9PG%12#J#`PeQ1EPGPOPeQ16PGPOPeQ0IPGPOPePkPGPOPeQ0JPGQ0<PeP?PGQ0zPeQ0WPGQ03PePhPG%;3R3#8Rh,?ePeQ15PG%1fRf#9#b#X#`%;p-0Te%B{#J#J#J#5R{%9iRi#BRp#=#BR?#0Rk#B#J#J#5602e20Se?%;?+0HPeP3PGPQC^%Fk#J#J#5:02Q{Q0M#0#J#5,EO%=r#B#5+0H%;pPcQ0O#jQ1mQ1C#=Q1DQ1H#PQ1JQ1I#P%1v#B%aUQ0L#F#X#BRU$0R&0;UQ0}#0#eRU#YQ18#0#eRv#0#<#5%1v#<#5PO%1U#5RUPG%8UPOQ0~#0RU#0Rv#0#Q#5PEQ02#:Rp%1v#l&01URU#Y%PUQ10#0RU#<Rv#YRrPOPrPGQ1;#1Rr#0R{#9Rk#1#5R3#8%Pv%1U#a#5RU1EOU@09hCQ12Q11#1RU#B+0Q%PU%0X#_#5Q19#0#JQ1=#<#5RX1EOw@09hCQ1>#FQ1<#1RC#0RU#9#5+0G%1URU#=$0;%1U#5RUPOPUPG%:D%1CRC#0RU#=%1U#5%bC%YkRkPOPkPG%;iRi#8&01{#5R{1EO{@09hD%Pr#BQ1:#Q#_#5Rr+0GQ17#P#J#5Q1?Q1Q#;602p1cNi&0=;3S5}r3S5}3DC3I3IDC3}3S9}Xw3I3I3S3IDC3I3IDCDCI0F3I7Iq7I}3I3II0F3SD@D3D3D3D3D3D3D3D3D3D3D3D3D3DCDCD3D3D3D3D3D3D3D3D3D3D3D3D3D3DCD3D3D3DCDCDCDCDCDCR}'|D@D@Rq'|D@D@RX3SD@D@M<x,N`Rw;6wS1D1f11R3/f1R1P3PdPcPIC[Rr;6rR;1f99Ri/f9RpPiPjQ0VPOCORh;6hS0V%1f#l$03#j>0004Rf=6=fRDP0P]Q0E008ZP4CMR{=6={S0EPcPIQ0QPjQ0SQ1\#1#G#8Rk'?RCPjPlQ1K#0#QRU#X#DRvPZQ1^#8,?eR?PnQ1XP?Q0yQ13Q0iQ0jQ0kQ1VP~PZQ0l#:Q0mQ0nQ0oQ0pQ0qQ0rQ1RPuPtQ1LPZPvPOQ0@PZPPQ0sQ0tQ0uQ0v00?s3ACnDWDW3A3A3ADW3ACnH0>P5PyPbQ1ZQ1[Q1]Q1_Q0TP|PTPgQ1bQ1cQ1dQ1eQ1fPeQ01#BPGPzQ1hQ1iQ1jQ1GQ1lPeQ00PGPOCKPeQ0Z#9PGPOPeQ0G#1Rz#FPGPOPe%0zRz#9Ru#0PGPOPeQ0H#9PGPOPe%9YPGPOPeQ0>#FPGQ0NPeQ0w#0PGQ1APeQ0Y#FPGQ1@PeQ1o#0PGPxPe%FSPG%9U#<#DPe%0\PGPtPeQ1NPGQ0P#9#<#`P}D3D3D3D3D3D3D3D3D3D3D3D33SD@D3D@D@D@D@R}M<x,N`RG=6aGS1lP3Q0QPcPIC[R\=61\S0Q1fp9RUPiPjPCPvCO=dpZRC;6CS0PPcPIPdPjPjPjPlPOPOPmQ1B1|bX9S5yM<x,N`RX=6aXS1NPiPjPjPOCORS=6pSS1oP0P]208VMQ0ACMRx=6=xS0APcPI%Fu#l#jRuPj1?ekRYPjPlPQPMP?PH%8uP?Q0yQ13Q0[Q0\Q0]Q1VP~PMQ0^#:Q0_Q0`Q0aQ0bQ0cQ0dPOPZPtPvPOPQPOQ0@Q14PPQ0eQ0fQ0gQ0h00?s3ACnDWDW3A3A3ADW3ACnH0>P}M<x,N`R}=6a}S0]P3PuPcPIC[Ru=61uS0\20PjYRs=diQS0`=dpMRM=6UMS0_PcPIPdPjPYPjPlPOPOPmQ1BP5PyPbQ1a%az#F#X#X#X#B#_#b#_#l$0J#580IFQ1MQ1OQ1PQ1SQ1TQ1WQ1YQ1ZQ1[Q1]Q1_Q0T1|gq9S|TD@D@D@D@M<x,N`RT=6aTS0TAdisORs=6psS1_/4DS1],4;S1['4S1Z,4_S1Y,4LS1W'4S1T'4S1S'4S1P'4R|,4DRq'4Rg,4;RF'4Rz,4_Rb'4Ry'4R5'4Rm'4Rl'4RY'4Rd'4RI'4Rc'4RP'4Rt'4R~'4R?'4R2'4P=PJPLP21k=KR2Q05P?P=P:Q0=P~P=PRQ0BPtP=PWQ0FPPP=P[P_Pc1k=^RcQ1DPIPaPwP;Pd1k1rRdQ0VPYPpPhPDPl1k=fRlQ0EPmP=P{Q1lP5PaPGQ0QPyP1P\Q0PPbPUPCP_PzPcQ1NPFPaPXP;PgPdQ1oPqPpPSPDP|PlQ0AQ1PP=PxQ0]Q1SPaP}Q0\Q1TP1PuQ0_Q1WPUPMPLQ1YP2P_Q1ZPcQ0TQ1[PaPTP;Q1]PdQ1_PDPpPsPlG]DLK0ODLDLDLG]G]G]DLDLDLG]G]G]DLDLDLG]DLP=P0P01f@0R@g00g\Rlg00hm3>RDP0PDPJP=P0P0g00j:9>@lRJP0PJPKP=P0P0g00kG9>@lRJP0PJP:P=P0P0g00lT9>@lR:P0P:P0P>P<Q06g00maR:>0<6ORJP:CZB056Q:/ENPBP<POH0E/{4CMP=P0P0g00nl9>@lRBP0PBP0P>P7P8PVP:CZP7Q0?P7PAPEP:H0D1iJOCZ/{4RJCMP=P0P0g01099>@lREP0PEP0P>Q0CQ0D<0C:/?VR>007ZP4CMP=P0P0g011F9>@lREP0PEP^Pag012Sg013a5rog014oRE,N`P1P3%oE%pE%qEC[PrPpPi%uE%tE%sECOPiPjB056e:ReQ0U'?POCOP=P0P0g016=9>@lRO1v0OCzPfP=P0P0g017J9>@lROP0POP0P]208>ZP4CMPag018Xg019g5rng01;6Rn,N`P1P3%on%pn%qnC[P\PUPi%un%tn&0BnCO%sn5dpPiPj1?ekPvCO=dpZP=P0P0g01<E9>@lRZ1v0ZCzP^Pag01=Sg01>b5rog01@1RZ,N`P1P3%oZ%pZ%qZC[PrPpPi%uZ%tZ%sZCOPSP=P0P0g01A@9>@lRS1v0SCzPfP=P0P0g01BN9>@lRSP0PSP0P]P<P8PVP:CZPJCMPag01C\g01Dk5rHg01F:RH,N`P1P3%oH%pH%qHC[PuPUPi%uH%tH&0BHCO%sH5dpPpP9Q0`P:CHP=P0P0g01GI9>@lR:1v0:CzPKP=P0P0g01HW9>@lRKP0PKP^Pag01Ieg01K45rog01LCRo,N`P1P3%oo%po%qoC[PrPpPi%uo%to%soCOPsP=P0g01MR9>@lRl-0M01v0lPfI0LH0KFTGRFTFTGRFTFTFTFTGRFTFTGRGRGRGRGRGRGRdo"). Qed.

End FPX_1.
