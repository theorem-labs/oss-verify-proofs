(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec SymExec2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymRun SymDrive SymDriveX RefMemcpyLib U.S0MainEntry SymDriveH4 U.S0LibStdioCall.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymRun OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDrive OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveX OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0MainEntry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SymDriveH4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0LibStdioCall.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SymFold.   (* [comment removed for export] *)
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition STOPS : list Z := [0x306ac; 0x30ab0; 0x30ba8; 0x30bec; 0x13208; 0x2aaa8; 0x291c0; 0x2b114]%Z.
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
Definition IHI : Z := 0x66000.
(* [comment removed for export] *)
Definition BUF_LO : Z := -560.   (* [comment removed for export] *)
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x13580 sr_main [] kn_main 38.
Definition rA__t := run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA__t)).
Definition rA := ltac:(SymFold.sf_def rA__t (srA, (kn_main, tt))).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_main.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (EVar 38).
Definition knB0 : list kentry :=
  KRange (EVar 2) 0x7fff80000000 0x800000400000
  :: KRange (EVar 38) (2 ^ 64 - 4095) (2 ^ 64 - 1) :: knA.
Definition ssB0 : sym_state := SS 0x30fd4 srB0 [] knB0 39.
Definition scrB : scripts := SCR [false] [] [].
Definition rB__t := run scrB ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB__t)).
Definition rB := ltac:(SymFold.sf_def rB__t (srB, (knB0, tt))).
Definition knB : list kentry := Eval vm_compute in kn_after rB knB0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-544)) 1 (ELit 32);
   SE (SA (EVar 0) (-552)) 8 (ELit 7954887939408031598);
   SE (SA (EVar 0) (-560)) 8 (ELit 7953747406983097443)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x2baf0 srC0 [] knC0 71.
Definition rC__t := run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC__t)).
Definition rC := ltac:(SymFold.sf_def rC__t (srC, (knC0, tt))).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0x2baf0 srD0 [] knC 103.
Definition rD__t := run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD__t)).
Definition rD := ltac:(SymFold.sf_def rD__t (srD, (knC, tt))).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
(* [comment removed for export] *)
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0x2c480 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE__t := run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE__t)).
Definition rE := ltac:(SymFold.sf_def rE__t (srE, (knE0, tt))).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0x2baf0 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF__t := run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF__t)).
Definition rF := ltac:(SymFold.sf_def rF__t (srF, (knE, tt))).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0x2baf0 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG__t := run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG__t)).
Definition rG := ltac:(SymFold.sf_def rG__t (srG, (knG0, tt))).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-543) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0x2baf0 srH0 [] knH0 231.
Definition rH__t := run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH__t)).
Definition rH := ltac:(SymFold.sf_def rH__t (srH, (knH0, tt))).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scOF__t : stdio_res := sc_of 231 srH knH.
Definition srI0 : list expr := Eval vm_compute in sc_sr scOF__t.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scOF__t.
Definition scOF : stdio_res := ltac:(SymFold.sf_def scOF__t (srI0, (knI0, tt))).

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS 0x2bde0 srI0 [] knI0 263.
Definition rI__t := run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI__t)).
Definition rI := ltac:(SymFold.sf_def rI__t (srI, (knI0, tt))).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrG3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition rG3__t := run scrG3 ssG0.
Definition srG3 : list expr := Eval vm_compute in s_regs (fst (fst rG3__t)).
Definition rG3 := ltac:(SymFold.sf_def rG3__t (srG3, (knG0, tt))).
Definition knG3 : list kentry := Eval vm_compute in kn_after rG3 knG0.
Definition scG3__t : stdio_res := sc_of 199 srG3 knG3.
Definition srH30 : list expr := Eval vm_compute in sc_sr scG3__t.
Definition knH30 : list kentry := Eval vm_compute in sc_kn scG3__t.
Definition scG3 : stdio_res := ltac:(SymFold.sf_def scG3__t (srH30, (knH30, tt))).
(* [comment removed for export] *)
Definition ssH30 : sym_state := SS (sc_ret scG3) srH30 [] knH30 231.
Definition rH3__t := run scr0 ssH30.
Definition srH3 : list expr := Eval vm_compute in s_regs (fst (fst rH3__t)).
Definition rH3 := ltac:(SymFold.sf_def rH3__t (srH3, tt)).
Definition knH3 : list kentry := Eval vm_compute in kn_after rH3 knH30.
Definition scH3__t : stdio_res := sc_of 231 srH3 knH3.
Definition srI30 : list expr := Eval vm_compute in sc_sr scH3__t.
Definition knI30 : list kentry := Eval vm_compute in sc_kn scH3__t.
Definition scH3 : stdio_res := ltac:(SymFold.sf_def scH3__t (srI30, (knI30, tt))).
(* [comment removed for export] *)
Definition ssI30 : sym_state := SS 0x2bde0 srI30 [] knI30 263.
Definition rI3__t := run scr0 ssI30.
Definition srI3 : list expr := Eval vm_compute in s_regs (fst (fst rI3__t)).
Definition rI3 := ltac:(SymFold.sf_def rI3__t (srI3, (knI30, tt))).
Definition knI3 : list kentry := Eval vm_compute in kn_after rI3 knI30.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition scrF4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition rF4__t := run scrF4 ssF0.
Definition srF4 : list expr := Eval vm_compute in s_regs (fst (fst rF4__t)).
Definition rF4 := ltac:(SymFold.sf_def rF4__t (srF4, (knE, tt))).
Definition knF4 : list kentry := Eval vm_compute in kn_after rF4 knE.
Definition scF4__t : stdio_res := sc_of 167 srF4 knF4.
Definition srG40 : list expr := Eval vm_compute in sc_sr scF4__t.
Definition knG40 : list kentry := Eval vm_compute in sc_kn scF4__t.
Definition scF4 : stdio_res := ltac:(SymFold.sf_def scF4__t (srG40, (knG40, tt))).
(* [comment removed for export] *)
Definition ssG40 : sym_state := SS (sc_ret scF4) srG40 [] knG40 199.
Definition rG4__t := run scr0 ssG40.
Definition srG4 : list expr := Eval vm_compute in s_regs (fst (fst rG4__t)).
Definition rG4 := ltac:(SymFold.sf_def rG4__t (srG4, tt)).
Definition knG4 : list kentry := Eval vm_compute in kn_after rG4 knG40.
(* [comment removed for export] *)
Definition logNL : list sentry := [SE (SA (EVar 0) (-560)) 1 (ELit 10)].
Definition knH40 : list kentry := Eval vm_compute in fst (fst (carry logNL knG4 [])).
Definition srH40 : list expr := Eval vm_compute in sr_after_call_j srG4 KEPT_MC 199.
(* [comment removed for export] *)
Definition ssH40 : sym_state := SS 0x2baf0 srH40 [] knH40 231.
Definition rH4__t := run scr0 ssH40.
Definition srH4 : list expr := Eval vm_compute in s_regs (fst (fst rH4__t)).
Definition rH4 := ltac:(SymFold.sf_def rH4__t (srH4, (knH40, tt))).
Definition knH4 : list kentry := Eval vm_compute in kn_after rH4 knH40.
Definition scH4__t : stdio_res := sc_of 231 srH4 knH4.
Definition srI40 : list expr := Eval vm_compute in sc_sr scH4__t.
Definition knI40 : list kentry := Eval vm_compute in sc_kn scH4__t.
Definition scH4 : stdio_res := ltac:(SymFold.sf_def scH4__t (srI40, (knI40, tt))).
(* [comment removed for export] *)
Definition ssI40 : sym_state := SS 0x2bde0 srI40 [] knI40 263.
Definition rI4__t := run scr0 ssI40.
Definition srI4 : list expr := Eval vm_compute in s_regs (fst (fst rI4__t)).
Definition rI4 := ltac:(SymFold.sf_def rI4__t (srI4, (knI40, tt))).
Definition knI4 : list kentry := Eval vm_compute in kn_after rI4 knI40.

Lemma itinerary_63_64 :
  (s_pc (fst (fst rG3)), snd (fst rG3))
     = (0x2b114%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ stdio_call 199 srG3 knG3 = Some scG3
  /\ (sc_ret scG3, sc_f scG3, sc_fd scG3) = (0x2bfb0%Z, 0x33db0%Z, 2%Z)
  /\ (sc_wb scG3, sc_wp scG3, sc_s scG3, sc_l scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-543)), ELit 0x10c4c, ELit 1)
  /\ (s_pc (fst (fst rH3)), snd (fst rH3)) = (0x2b114%Z, [])
  /\ stdio_call 231 srH3 knH3 = Some scH3
  /\ (sc_ret scH3, sc_f scH3, sc_fd scH3) = (0x2bde0%Z, 0x33db0%Z, 2%Z)
  /\ (sc_wb scH3, sc_wp scH3, sc_l scH3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst rI3)), snd (fst rI3)) = (0x291c0%Z, [])
  /\ (s_pc (fst (fst rF4)), snd (fst rF4))
     = (0x2b114%Z, [SCBr false BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ stdio_call 167 srF4 knF4 = Some scF4
  /\ (sc_ret scF4, sc_f scF4, sc_fd scF4) = (0x2c9d0%Z, 0x33db0%Z, 2%Z)
  /\ (sc_wb scF4, sc_wp scF4, sc_s scF4, sc_l scF4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-543)), EVar 2, PX)
  /\ (s_pc (fst (fst rG4)), snd (fst rG4)) = (0x306ac%Z, [])
  /\ (s_pc (fst (fst rH4)), snd (fst rH4)) = (0x2b114%Z, [])
  /\ stdio_call 231 srH4 knH4 = Some scH4
  /\ (sc_ret scH4, sc_f scH4, sc_fd scH4) = (0x2bde0%Z, 0x33db0%Z, 2%Z)
  /\ (sc_wb scH4, sc_wp scH4, sc_l scH4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-559)), ELit 0)
  /\ (s_pc (fst (fst rI4)), snd (fst rI4)) = (0x291c0%Z, []).
Proof. repeat match goal with |- _ /\ _ => split end; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.   (* [comment removed for export] *)

Lemma itinerary_le62 :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x30fd0%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB))
     = (0x306ac%Z, [SCBr false BC_LTU (EAluw ALU_ADD (EVar 38) (ELit 0)) (ELit 18446744073709547521)])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x306ac%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x30ba8%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x306ac%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x306ac%Z, [SCBr true BC_GEU (ELit 63) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x306ac%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 63)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x2b114%Z, [])
  /\ stdio_call 231 srH knH = Some scOF
  /\ (sc_ret scOF, sc_f scOF, sc_fd scOF) = (0x2bde0%Z, 0x33db0%Z, 2%Z)
  /\ (sc_wb scOF, sc_wp scOF, sc_l scOF)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-542)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x291c0%Z, []).
Proof. repeat match goal with |- _ /\ _ => split end; lazymatch goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.   (* [comment removed for export] *)
