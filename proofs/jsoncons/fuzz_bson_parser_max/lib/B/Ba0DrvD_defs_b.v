(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvRead_b Ba0DrvG_defs_b Ba0DrvC_defs_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition STOPS_TA : list Z := 0xa7e8c :: 0xa7c78 :: STOPSA.
Definition runTA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_TA scr ss [].

(* [comment removed for export] *)
Definition knTcA (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0A.
Definition rT00 := Eval vm_compute in runTA scr0 (SS 0xa7dd4 srT0A [] (knTcA 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runTA scr0 (SS 0xa7dd4 srT0A [] (knTcA 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runTA scr0 (SS 0xa7dd4 srT0A [] (knTcA 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runTA scr0 (SS 0xa7dd4 srT0A [] (knTcA 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
Definition calls_xA : expr := Eval vm_compute in nth 21 sr11 (ELit 0).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_case_entryA (K : kentry) : bool :=
  existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncaseA (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entryA K)) kn.
Definition knTeA : list kentry := Eval vm_compute in uncaseA (kn_after rT11 (knTcA 1 32767 1 67108857)).
(* [comment removed for export] *)
Definition TSO : Z := -208.
Definition knTkA : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knTeA.

(* [comment removed for export] *)
Definition srTm0A : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0A : list expr := Eval vm_compute in sr_after_call_j srTm0A (map ridx c_kept) 82.
Definition knU0A : list kentry := Eval vm_compute in kn_blk2A 92 ++ knTkA.
Definition rUA := Eval vm_compute in runTA scr0 (SS 0xa7e38 srU0A [] knU0A 114).
Definition srUA : list expr := Eval vm_compute in s_regs (fst (fst rUA)).
(* [comment removed for export] *)
Definition srV0A : list expr := Eval vm_compute in sr_after_call_j srUA (map ridx c_kept) 114.
Definition knV0A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knU0A.
Definition rVA := Eval vm_compute in runTA scr0 (SS 0xa7e4c srV0A [] knV0A 146).
Definition srVA : list expr := Eval vm_compute in s_regs (fst (fst rVA)).

(* [comment removed for export] *)
Definition spxA (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition knLH1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knTkA.
Definition srLHA : list expr :=
  [ELit 0; EVar 85; spxA (-208); ELit 67584; ELit 6765824; EVar 86; EVar 87; EVar 88;
   EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
   EVar 83; EVar 84; ELit 6759056; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 97; EVar 98; EVar 99; EVar 100].
(* [comment removed for export] *)
Definition shared_posA : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_bA (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLHA (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_posA.

(* [comment removed for export] *)
Definition rLB1A := Eval vm_compute in runTA scr0 (SS 0xa7e8c srLHA [] knLH1A 102).
Definition srLBA : list expr := Eval vm_compute in s_regs (fst (fst rLB1A)).
Definition knLc1A : list kentry := Eval vm_compute in kn_after rLB1A knLH1A.
Definition flag1A : list sentry := [SE (SA (ELit 0) 0x672294) 1 (ELit 1)].
Definition flag0A : list sentry := [SE (SA (ELit 0) 0x672294) 1 (ELit 0)].
(* [comment removed for export] *)
Definition LIBSTK : Z := 1048576.
Definition srLr0A : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLBA (map ridx c_kept) 102) (ridx 10) (ELit 0).

Lemma tgt_itinerary_okA :
  (s_pc (fst (fst rT00)), s_pc (fst (fst rT10)), s_pc (fst (fst rT01)), s_pc (fst (fst rT11))) = (0xa7e8c, 0xa7e8c, 0x79818, 0x79818)
  /\ ksubl_b (kn_after rT00 (knTcA 0 0 0 0)) knTeA = true /\ ksubl_b (kn_after rT01 (knTcA 0 0 1 67108857)) knTeA = true
  /\ ksubl_b (kn_after rT10 (knTcA 1 32767 0 0)) knTeA = true /\ ksubl_b (kn_after rT11 (knTcA 1 32767 1 67108857)) knTeA = true
  /\ sr_upd sr01 (ridx 21) (EVar 81) = srTm0A
  /\ ksubl_b knTeA knLH1A = true /\ ksubl_b knV0A knLH1A = true /\ kn_after rVA knV0A = knV0A /\ kn_after rUA knU0A = knU0A
  /\ relay_ok_bA (sr_upd sr00 (ridx 21) (EVar 81)) = true /\ relay_ok_bA (sr_upd sr10 (ridx 21) (EVar 81)) = true /\ relay_ok_bA srVA = true
  /\ kn_vars_lt 82 knLH1A = true /\ sr_vars_lt 82 srTm0A = true
  /\ (s_pc (fst (fst rUA)), snd (fst rUA), s_log (fst (fst rUA))) = (0x77c90, [], [])
  /\ (s_pc (fst (fst rVA)), snd (fst rVA), s_log (fst (fst rVA))) = (0xa7e8c, [], [])
  /\ (s_pc (fst (fst rLB1A)), s_log (fst (fst rLB1A))) = (0xa7fa4, flag1A)
  /\ kn_after rLB1A knLH1A = knLc1A
  /\ (nth 10 srLBA (ELit 0), nth 11 srLBA (ELit 0), nth 1 srLBA (ELit 0), nth 2 srLBA (ELit 0)) = (EVar 82, EVar 79, ELit 0xa7ea0, spxA (-208)).
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
