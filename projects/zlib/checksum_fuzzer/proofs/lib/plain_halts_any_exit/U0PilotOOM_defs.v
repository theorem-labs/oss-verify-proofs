(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib U0MainEntry U0LibStdioCall.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Tgt_checksum_fuzzer_ubsan.M.loaded_segments.

Definition kn_exec : list kentry := kn_main.

Definition STOPS : list Z := [0x1cf88; 0x1d38c; 0x1d484; 0x1d4c8; 0x14210; 0x176f0; 0x15e08; 0x18390]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run {RCa1 : RunCtx}  (scr : scripts) (ss : sym_state) := sym_exec (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition ssA0 : sym_state := SS 0x13d70 sr_main [] kn_exec 40.
Definition rA {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssA0.
Definition srA {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rA kn_exec.
Definition logA {RCa1 : RunCtx}  : list sentry := Eval vm_compute in s_log (fst (fst rA)).

Definition srB0 {RCa1 : RunCtx}  : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 {RCa1 : RunCtx}  : sym_state := SS 0x1d8b0 srB0 [] knA 40.
Definition rB {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssB0.
Definition srB {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rB knA.

Definition mc_store : sentry := SE (SA (EVar 0) (-384)) 8 (EVar 7).
Definition knB2 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in fst (fst (carry [mc_store] knB [])).
Definition srC0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srB (map ridx callee_kept) 40.

(* port727 (): musl's get_random_secret scans the auxv to its 0 key, and at the vector's
   tail past AT_EXECFN depends on the kernel build (CONFIG_RSEQ adds two pairs). So run C starts over
   knB2 ++ kn_auxv_tail rs (S0MainEntry; rs = kb_rseq (in_kernel inp)). Both runs stop at the brk ecall 0x16670 with
   the same registers except a2 (the loop pointer, dead after the call); after run D the registers agree and the
   knowledge agrees once the tail entries are dropped (is_tail_k). The names below are the rs = false run; the
   proof replays both runs and joins at knD (S0PilotOOM.oom_seg2c / oom_seg2b). *)
Definition is_tail_k (k : kentry) : bool :=
  match k with
  | KWord (SA (EVar 3) o) _ _ => (416 <=? o)%Z
  | KDisj _ _ (SA (EVar 3) o) _ => (416 <=? o)%Z
  | _ => false
  end.
Definition drop_tail (kn : list kentry) : list kentry := List.filter (fun k => negb (is_tail_k k)) kn.
Definition knC0 {RCa1 : RunCtx}  (rs : bool) : list kentry := knB2 ++ kn_auxv_tail rs.
Definition ssC0 {RCa1 : RunCtx}  : sym_state := SS 0x16880 srC0 [] (knC0 false) 72.
Definition rC {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssC0.
Definition srC {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rC (knC0 false).

Definition b_expr : expr := EVar 72.
Definition knD0 {RCa1 : RunCtx}  : list kentry := KAlign b_expr 4096 :: KRange b_expr 0x51000 0x80030000 :: knC.
Definition srD0 {RCa1 : RunCtx}  : list expr := sr_upd srC (ridx 10) b_expr.
Definition ssD0 {RCa1 : RunCtx}  : sym_state := SS 0x1694c srD0 [] knD0 73.
Definition rD {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssD0.
Definition srD {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD {RCa1 : RunCtx}  : list kentry := Eval vm_compute in drop_tail (kn_after rD knD0).
(* the rs = true run lands on the same registers and, without its tail entries, the same knowledge *)
Lemma runD_rseq_agrees {RCa1 : RunCtx}  :
  let rCt := run scr0 (SS 0x16880 srC0 [] (knC0 true) 72) in
  let knD0t := KAlign b_expr 4096 :: KRange b_expr 0x51000 0x80030000 :: kn_after rCt (knC0 true) in
  let rDt := run scr0 (SS 0x1694c (sr_upd (s_regs (fst (fst rCt))) (ridx 10) b_expr) [] knD0t 73) in
  s_regs (fst (fst rDt)) = srD /\ drop_tail (kn_after rDt knD0t) = knD.
Proof. vm_compute. split; reflexivity. Qed.
Definition ugly_b : expr :=
  EAlu ALU_ADD b_expr (EAlu ALU_AND (ELit 4095) (EMd M_MUL (ELit (-1)) b_expr)).
Definition srD2 {RCa1 : RunCtx}  : list expr := Eval vm_compute in map (esub ugly_b b_expr) srD.
Definition knD2 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in map (ksub ugly_b b_expr) knD.

Definition srE0 {RCa1 : RunCtx}  : list expr := sr_upd srD2 (ridx 10) b_expr.
Definition ssE0 {RCa1 : RunCtx}  : sym_state := SS 0x16970 srE0 [] knD2 73.
Definition scrE : scripts := SCR [true] [] [].
Definition rE {RCa1 : RunCtx}  := Eval vm_compute in run scrE ssE0.
Definition srE {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rE knD2.

Definition srF0 {RCa1 : RunCtx}  : list expr := sr_upd srE (ridx 10) (ELit (2 ^ 64 - 12)).
Definition ssF0 {RCa1 : RunCtx}  : sym_state := SS 0x17a84 srF0 [] knE 73.
Definition rF {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssF0.
Definition srF {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rF knE.

Definition resG_opt {RCa1 : RunCtx}  : option stdio_res := Eval vm_compute in stdio_call 73 srF knF.
Definition resG {RCa1 : RunCtx}  : stdio_res :=
  Eval vm_compute in match resG_opt with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma resG_eq {RCa1 : RunCtx}  : stdio_call 73 srF knF = Some resG.
Proof. vm_compute. reflexivity. Qed.

Definition srG0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr resG.
Definition knG0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn resG.
Definition ssG0 {RCa1 : RunCtx}  : sym_state := SS 0x180fc srG0 [] knG0 105.
Definition rG {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssG0.
Definition srG {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rG knG0.

