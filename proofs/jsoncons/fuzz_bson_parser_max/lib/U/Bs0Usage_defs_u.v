(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SymDriveH4.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0LibStdioCall_u Bs0OpenFail_defs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0MainEntryN_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x3427c sr_mainN [] kn_mainN 38.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 38.

(* [comment removed for export] *)
Definition u_ssB0 : sym_state := SS 0xa0734 u_srB0 [] u_knB0 70.
Definition u_rB := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 70.

(* [comment removed for export] *)
Definition u_ssC0 : sym_state := SS 0xa0734 u_srC0 [] u_knB 102.
Definition u_rC := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 112.
Definition u_knD0 : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 102.

(* [comment removed for export] *)
Definition u_ssD0 : sym_state := SS 0xa12a4 u_srD0 [] u_knD0 134.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 134.

(* [comment removed for export] *)
Definition u_ssE0 : sym_state := SS 0xa0734 u_srE0 [] u_knD 166.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 166.

(* [comment removed for export] *)
Definition u_ssF0 : sym_state := SS 0xa0734 u_srF0 [] u_knF0 198.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 198.
(* [comment removed for export] *)
Definition u_ssG0 : sym_state := SS 0xa0734 u_srG0 [] u_knG0 230.
Definition u_rG := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG : stdio_res := Eval vm_compute in sc_of 230 u_srG u_knG.
Definition u_srH0 : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 : sym_state := SS 0xa0c04 u_srH0 [] u_knH0 262.
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
Definition u_ssH30 : sym_state := SS 0xa0c04 u_srH30 [] u_knH30 262.
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
Definition u_ssG40 : sym_state := SS 0xa0734 u_srG40 [] u_knG40 230.
Definition u_rG4 := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 : stdio_res := Eval vm_compute in sc_of 230 u_srG4 u_knG4.
Definition u_srH40 : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 : sym_state := SS 0xa0c04 u_srH40 [] u_knH40 262.
Definition u_rH4 := Eval vm_compute in run scr0 u_ssH40.
Definition u_srH4 : list expr := Eval vm_compute in s_regs (fst (fst u_rH4)).
Definition u_knH4 : list kentry := Eval vm_compute in kn_after u_rH4 u_knH40.

Lemma u_itinerary :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0xab480%Z, [SCBr true BC_NE (EVar 16) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0xab480%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0xabf74%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0xab480%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0xab480%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0xab480%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0x9ff58%Z, [])
  /\ stdio_call 230 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0xa0c04%Z, 0xb8300%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x9adf0%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0x9ff58%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 198 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0xa0dd4%Z, 0xb8300%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x1101a, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0x9ff58%Z, [])
  /\ stdio_call 230 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0xa0c04%Z, 0xb8300%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x9adf0%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0x9ff58%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 166 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0xa17f4%Z, 0xb8300%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0xab480%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0x9ff58%Z, [])
  /\ stdio_call 230 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0xa0c04%Z, 0xb8300%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x9adf0%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
