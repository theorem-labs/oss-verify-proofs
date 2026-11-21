(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib U7MainEntry SymDriveH4 U7LibStdioCall.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments.

Definition STOPS : list Z := [0x21470; 0x21874; 0x2196c; 0x219b0; 0x14d9c; 0x1bcac; 0x1a3a8; 0x1c878]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run {RCa1 : RunCtx}  (scr : scripts) (ss : sym_state) := sym_exec (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition sc_of {RCa1 : RunCtx}  (nv : nat) (sr : list expr) (kn : list kentry) : stdio_res :=
  match stdio_call nv sr kn with
  | Some r => r
  | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] []
  end.
Definition KEPT_MC : list nat := map ridx callee_kept.
Definition KEPT_CS : list nat := map ridx callee_saved.
Definition IHI : Z := 0x95000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

Definition ssA0 : sym_state := SS 0x148fc sr_main [] kn_main 40.
Definition rA {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssA0.
Definition srA {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rA kn_main.

Definition srB0 {RCa1 : RunCtx}  : list expr := sr_upd srA (ridx 10) (EVar 40).
Definition knB0 {RCa1 : RunCtx}  : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 40) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 {RCa1 : RunCtx}  : sym_state := SS 0x21d98 srB0 [] knB0 41.
Definition scrB : scripts := SCR [false] [] [].
Definition rB {RCa1 : RunCtx}  := Eval vm_compute in run scrB ssB0.
Definition srB {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rB knB0.
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 41.

Definition ssC0 {RCa1 : RunCtx}  : sym_state := SS 0x1c528 srC0 [] knC0 73.
Definition rC {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssC0.
Definition srC {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 73.

Definition ssD0 {RCa1 : RunCtx}  : sym_state := SS 0x1c528 srD0 [] knC 105.
Definition rD {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssD0.
Definition srD {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 115.
Definition knE0 {RCa1 : RunCtx}  : list kentry := KRange PX 0 131155 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 105.

Definition ssE0 {RCa1 : RunCtx}  : sym_state := SS 0x1d278 srE0 [] knE0 137.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE {RCa1 : RunCtx}  := Eval vm_compute in run scrE ssE0.
Definition srE {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 137.

Definition ssF0 {RCa1 : RunCtx}  : sym_state := SS 0x1c528 srF0 [] knE 169.
Definition scrF : scripts := SCR [true; true] [] [].
Definition rF {RCa1 : RunCtx}  := Eval vm_compute in run scrF ssF0.
Definition srF {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 169.

Definition ssG0 {RCa1 : RunCtx}  : sym_state := SS 0x1c528 srG0 [] knG0 201.
Definition scrG : scripts := SCR [true] [] [].
Definition rG {RCa1 : RunCtx}  := Eval vm_compute in run scrG ssG0.
Definition srG {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 201.

Definition ssH0 {RCa1 : RunCtx}  : sym_state := SS 0x1c528 srH0 [] knH0 233.
Definition rH {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssH0.
Definition srH {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rH knH0.
Definition scOF {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 233 srH knH.
Definition srI0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr scOF.
Definition knI0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn scOF.

Definition ssI0 {RCa1 : RunCtx}  : sym_state := SS 0x1cbd8 srI0 [] knI0 265.
Definition rI {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssI0.
Definition srI {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rI knI0.

Definition scrG3 : scripts := SCR [false] [] [].
Definition rG3 {RCa1 : RunCtx}  := Eval vm_compute in run scrG3 ssG0.
Definition srG3 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rG3)).
Definition knG3 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 201 srG3 knG3.
Definition srH30 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr scG3.
Definition knH30 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn scG3.
Definition ssH30 {RCa1 : RunCtx}  : sym_state := SS (sc_ret scG3) srH30 [] knH30 233.
Definition rH3 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssH30.
Definition srH3 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rH3)).
Definition knH3 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 233 srH3 knH3.
Definition srI30 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr scH3.
Definition knI30 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn scH3.
Definition ssI30 {RCa1 : RunCtx}  : sym_state := SS 0x1cbd8 srI30 [] knI30 265.
Definition rI3 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssI30.

Definition scrF4 : scripts := SCR [true; false] [] [].
Definition rF4 {RCa1 : RunCtx}  := Eval vm_compute in run scrF4 ssF0.
Definition srF4 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rF4)).
Definition knF4 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 169 srF4 knF4.
Definition srG40 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr scF4.
Definition knG40 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn scF4.
Definition ssG40 {RCa1 : RunCtx}  : sym_state := SS (sc_ret scF4) srG40 [] knG40 201.
Definition rG4 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssG40.
Definition srG4 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rG4)).
Definition knG4 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rG4 knG40.
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 201.
Definition ssH40 {RCa1 : RunCtx}  : sym_state := SS 0x1c528 srH40 [] knH40 233.
Definition rH4 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssH40.
Definition srH4 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rH4)).
Definition knH4 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 233 srH4 knH4.
Definition srI40 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr scH4.
Definition knI40 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn scH4.
Definition ssI40 {RCa1 : RunCtx}  : sym_state := SS 0x1cbd8 srI40 [] knI40 265.
Definition rI4 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssI40.

Lemma itinerary_63_64 {RCa1 : RunCtx}  :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0x1c878%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 201 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x1cda8%Z, 0x23f30%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x1049b, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x1c878%Z, [])
  /\ stdio_call 233 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x1cbd8%Z, 0x23f30%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x1a3a8%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0x1c878%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 169 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x1d7c8%Z, 0x23f30%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x21470%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x1c878%Z, [])
  /\ stdio_call 233 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x1cbd8%Z, 0x23f30%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x1a3a8%Z, []).
Proof.
  repeat apply conj; lazymatch goal with |- @eq ?T ?x ?y => vm_cast_no_check (@eq_refl T y) end.
Qed.

Lemma itinerary_le62 {RCa1 : RunCtx}  :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x21d94%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x21470%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 40) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x21470%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x2196c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x21470%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x21470%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x21470%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x1c878%Z, [])
  /\ stdio_call 233 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x1cbd8%Z, 0x23f30%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x1a3a8%Z, []).
Proof.
  repeat apply conj; lazymatch goal with |- @eq ?T ?x ?y => vm_cast_no_check (@eq_refl T y) end.
Qed.
