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
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib HUMainEntryDefs HULibStdioCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)

Import ListNotations. Import SX2. Import SX2S.
Import ConeCfg.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition is_kblob (K : kentry) : bool := match K with KBlob _ _ _ => true | _ => false end.
Definition kn_main_noblob : list kentry := List.filter (fun K => negb (is_kblob K)) kn_main.
Definition kn_rndcan : list kentry :=
  [KWord (SA (EVar 4) 0) 8 (EVar 38); KWord (SA (EVar 4) 8) 8 (EVar 39);
   KWord (SA (ELit 0) 0x331ad8) 8 (EVar 40); KWord (SA (ELit 0) 0x351b28) 8 (EVar 40)].
Definition kn_exec : list kentry := Eval vm_compute in (kn_main_noblob ++ kn_rndcan).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS : list Z := [0x2bc024; 0x2bc5a4; 0x2bccb0; 0x2bbf28; 0xe1e7c; 0x2b31f4; 0x2b17ec; 0x2b55ac]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0xe1984 sr_main [] kn_exec 41.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_exec.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x2bd1e0 srB0 [] knA 41.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
Definition mc_store : sentry := SE (SA (EVar 0) (-384)) 8 (EVar 39).
Definition knB2 : list kentry := Eval vm_compute in fst (fst (carry [mc_store] knB [])).
(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB (map ridx callee_kept) 41.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x2b2384 srC0 [] knB2 73.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knB2.

(* [comment removed for export] *)
Definition b_expr : expr := EVar 73.
Definition knD0 : list kentry := KAlign b_expr 4096 :: KRange b_expr 0x354000 0x80354000 :: knC.
Definition srD0 : list expr := sr_upd srC (ridx 10) b_expr.
Definition ssD0 : sym_state := SS 0x2b2450 srD0 [] knD0 74.
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
Definition ssE0 : sym_state := SS 0x2b2474 srE0 [] knD2 74.
Definition scrE : scripts := SCR [true] [] [].     (* [comment removed for export] *)
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knD2.

(* [comment removed for export] *)
Definition srF0 : list expr := sr_upd srE (ridx 10) (ELit (2 ^ 64 - 12)).
Definition ssF0 : sym_state := SS 0x2b3e24 srF0 [] knE 74.
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
Definition ssG0 : sym_state := SS 0x2b5f50 srG0 [] knG0 106.
Definition rG := Eval vm_compute in run scr0 ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.

(* [comment removed for export] *)
Lemma itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x2bd1dc%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB)) = (0x2bc024%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x2b244c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x2b2470%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE)) = (0x2b3e20%Z, [SCBr true BC_NE b_expr (EAlu ALU_ADD b_expr (ELit 8192))])
  /\ (s_pc (fst (fst rF)), snd (fst rF)) = (0x2b55ac%Z, [])
  /\ (sc_ret resG, sc_f resG, sc_fd resG) = (0x2b5f50%Z, 0x31ebd0%Z, 2%Z)
  /\ (s_pc (fst (fst rG)), snd (fst rG)) = (0x2b17ec%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
