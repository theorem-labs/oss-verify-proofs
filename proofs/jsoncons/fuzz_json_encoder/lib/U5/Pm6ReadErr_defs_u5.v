(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6MainEntry_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SymDriveH4. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6LibStdioCall_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}.


Definition STOPS : list Z := [0xbe048; 0xbe5c8; 0xbeb3c; 0xbdf4c; 0xad0c4; 0xad250; 0xb117c; 0xad914; 0xb2bb8]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0xfe000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0xdd010; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0xcb000) 0x33000;
   KImg 0x10000 0xcb538; KImg 0xcb541 0xcb589; KImg 0xdb589 0xdcf40; KImg 0xfd018 0xfd038;
   KWord (SA (ELit 0) 0xdcf48) 8 (ELit 0xdcf48);
   KWord (SA (ELit 0) 0xdcf68) 4 (EVar 5);
   KImg 0xdcf74 0xdcfc0; KImg 0xdcfc8 0xdcfe0; KImg 0xdcfe8 0xdd000;
   KImg 0xdd010 0xdd020; KImg 0xdd028 0xfd018; KImg 0xfd050 0xfd280;
   KBlob (SA (ELit 0) 0xfd280) (ELit 8) 2;
   KImg 0xfd288 0xfd290; KImg 0xfd2a1 0xfd2a8; KImg 0xfd2b0 0xfd2b8; KImg 0xfd2c8 0xfd2d0;
   KWord (SA (ELit 0) 0xfd2d0) 8 (ELit 4096);
   KImg 0xfd2d8 0xfd308;
   KImg 0xfd7d8 0xfe000;   (* [comment removed for export] *)
   KRange (EVar 5) 1 4194303].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x3a39c srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0xb3394 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xb3394 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xb3f04 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xb3394 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xb3394 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xb3394 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xbe048%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xbe048%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xbeb3c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xbe048%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xbe048%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xbe048%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xb2bb8%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0xb3864%Z, 0xcb338%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0xad914%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.


End FPX_1.
