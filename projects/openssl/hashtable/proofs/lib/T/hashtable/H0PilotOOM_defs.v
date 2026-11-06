(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.openssl.hashtable.images Require Import Plain.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib H0MainEntryDefs H0LibStdioCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

Import ListNotations. Import SX2. Import SX2S.
Import ConeCfg.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition is_kblob (K : kentry) : bool := match K with KBlob _ _ _ => true | _ => false end.
Definition kn_main_noblob : list kentry := List.filter (fun K => negb (is_kblob K)) kn_main.
Definition kn_rndcan : list kentry :=
  [KWord (SA (EVar 4) 0) 8 (EVar 38); KWord (SA (EVar 4) 8) 8 (EVar 39);
   KWord (SA (ELit 0) 0x2ebf48) 8 (EVar 40); KWord (SA (ELit 0) 0x30bf98) 8 (EVar 40)].
Definition kn_exec : list kentry := Eval vm_compute in (kn_main_noblob ++ kn_rndcan).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS : list Z := [0x27647c; 0x2769fc; 0x277108; 0x276380; 0xdd594; 0x26d64c; 0x26bc44; 0x26fa04]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0xdd09c sr_main [] kn_exec 41.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_exec.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x277638 srB0 [] knA 41.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
Definition mc_store : sentry := SE (SA (EVar 0) (-384)) 8 (EVar 39).
Definition knB2 : list kentry := Eval vm_compute in fst (fst (carry [mc_store] knB [])).
(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB (map ridx callee_kept) 41.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x26c7dc srC0 [] knB2 73.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knB2.

(* [comment removed for export] *)
Definition b_expr : expr := EVar 73.
Definition knD0 : list kentry := KAlign b_expr 4096 :: KRange b_expr 0x30e000 0x8030e000 :: knC.
Definition srD0 : list expr := sr_upd srC (ridx 10) b_expr.
Definition ssD0 : sym_state := SS 0x26c8a8 srD0 [] knD0 74.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knD0.
(* [comment removed for export] *)
Definition ugly_b : expr :=
  EAlu ALU_ADD b_expr (EAlu ALU_AND (ELit 4095) (EMd M_MUL (ELit (-1)) b_expr)).
Definition srD2 : list expr := Eval vm_compute in map (esub ugly_b b_expr) srD.
Definition knD2 : list kentry := Eval vm_compute in map (ksub ugly_b b_expr) knD.

(* [comment removed for export] *)
Definition srE0 : list expr := sr_upd srD2 (ridx 10) b_expr.
Definition ssE0 : sym_state := SS 0x26c8cc srE0 [] knD2 74.
Definition scrE : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD2.

(* [comment removed for export] *)
Definition srF0 : list expr := sr_upd srE (ridx 10) (ELit (2 ^ 64 - 12)).
Definition ssF0 : sym_state := SS 0x26e27c srF0 [] knE 74.
Definition rF := Eval vm_compute in run scr0 ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.

(* [comment removed for export] *)
Definition resG_opt : option stdio_res := Eval vm_compute in stdio_call 74 srF knF.
Definition resG : stdio_res :=
  Eval vm_compute in match resG_opt with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma resG_eq : stdio_call 74 srF knF = Some resG.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition srG0 : list expr := Eval vm_compute in sc_sr resG.
Definition knG0 : list kentry := Eval vm_compute in sc_kn resG.
Definition ssG0 : sym_state := SS 0x2703a8 srG0 [] knG0 106.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.

(* [comment removed for export] *)
Lemma itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x277634%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB)) = (0x27647c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x26c8a4%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x26c8c8%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x26e278%Z, [SCBr true BC_NE b_expr (EAlu ALU_ADD b_expr (ELit 8192))])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x26fa04%Z, [])
  /\ (sc_ret resG, sc_f resG, sc_fd resG) = (0x2703a8%Z, 0x2d9040%Z, 2%Z)
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x26bc44%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
