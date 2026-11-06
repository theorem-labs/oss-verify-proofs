(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive LibKnowFrame.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import RefExitBase RefStdioDefs AsStdioCall AsPrintfFirst.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsCarryKeep.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsExitDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rX1c1 := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS AEXIT x_sr [] (ax_kn false false) 40) []).
Definition srX1c1 := Eval vm_compute in (s_regs (fst (fst rX1c1))).
Definition cX1c1 := Eval vm_compute in (carry (s_log (fst (fst rX1c1))) (ax_kn false false) []).
Definition knX1c1 := Eval vm_compute in (fst (fst cX1c1)).
(* [comment removed for export] *)
Definition srX2ic1 := Eval vm_compute in (sr_upd (sr_upd srX1c1 (ridx 14) (ELit 0)) (ridx 15) (ELit 0)).
Definition cX2ic1 := Eval vm_compute in (carry [SE (SA (ELit 0) 0x67d720) 4 (sr_get srX1c1 12)] knX1c1 []).
Definition knX2ic1 := Eval vm_compute in (fst (fst cX2ic1)).
(* [comment removed for export] *)
Definition rX2c1 := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x0ff2d8 srX2ic1 [] knX2ic1 40) []).
Definition srX2c1 := Eval vm_compute in (s_regs (fst (fst rX2c1))).
Definition cX2c1 := Eval vm_compute in (carry (s_log (fst (fst rX2c1))) knX2ic1 []).
Definition knX2c1 := Eval vm_compute in (fst (fst cX2c1)).
(* [comment removed for export] *)
Definition srX3ic1 := Eval vm_compute in (sr_upd (sr_upd srX2c1 (ridx 13) (sr_get srX2c1 12)) (ridx 15) (ELit 0)).
Definition cX3ic1 := Eval vm_compute in (carry [SE (SA (ELit 0) 0x126d30) 8 (sr_get srX2c1 14)] knX2c1 []).
Definition knX3ic1 := Eval vm_compute in (fst (fst cX3ic1)).
(* [comment removed for export] *)
Definition rX3c1 := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5d9f4 srX3ic1 [] knX3ic1 40) []).
Definition srX3c1 := Eval vm_compute in (s_regs (fst (fst rX3c1))).
Definition cX3c1 := Eval vm_compute in (carry_keep keep_nonshadow (s_log (fst (fst rX3c1))) knX3ic1 []).
Definition knX3c1 := Eval vm_compute in (kn_drop_shadow (fst (fst cX3c1))).
(* [comment removed for export] *)
Definition srX4ic1 := Eval vm_compute in (sr_upd (sr_upd srX3c1 (ridx 6) (sr_get srX3c1 10)) (ridx 7) (ELit 0)).
Definition cX4ic1 := Eval vm_compute in (carry [SE (SA (ELit 0) 0x126d30) 8 (sr_get srX3c1 5)] knX3c1 []).
Definition knX4ic1 := Eval vm_compute in (fst (fst cX4ic1)).
(* [comment removed for export] *)
Definition rX4c1 := Eval vm_compute in (sym_exec RSEGS XFUEL true XSTOPS scr0 (SS 0x5dd64 srX4ic1 [] knX4ic1 40) []).
Definition srX4c1 := Eval vm_compute in (s_regs (fst (fst rX4c1))).
Definition cX4c1 := Eval vm_compute in (carry (s_log (fst (fst rX4c1))) knX4ic1 []).
Definition knX4c1 := Eval vm_compute in (fst (fst cX4c1)).

Lemma x_itinerary_clean1 :
  s_pc (fst (fst rX1c1)) = 0x0ff2cc /\ snd (fst rX1c1) = [] /\ snd (fst cX1c1) = []
  /\ snd (fst cX2ic1) = [] /\ kread RSEGS knX1c1 (ELit 0) 0x67d720 4 = Some (ELit 0)
  /\ s_pc (fst (fst rX2c1)) = 0x5d9e8 /\ snd (fst rX2c1) = [] /\ snd (fst cX2c1) = []
  /\ snd (fst cX3ic1) = [] /\ kread RSEGS knX2c1 (ELit 0) 0x126d30 8 = Some (sr_get srX2c1 12)
  /\ s_pc (fst (fst rX3c1)) = 0x5dd58 /\ snd (fst rX3c1) = [] /\ snd (fst cX3c1) = []
  /\ snd (fst cX4ic1) = [] /\ kread RSEGS knX3c1 (ELit 0) 0x126d30 8 = Some (sr_get srX3c1 10)
  /\ s_pc (fst (fst rX4c1)) = AEXIT_ECALL /\ snd (fst rX4c1) = [] /\ snd (fst cX4c1) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.
