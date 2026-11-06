(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymAux.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section FX.
Context {fx : FPState}.

Definition TR_ENTRY : Z := 0x658b8.
Definition TR_POSTINIT : Z := 0x65900.
Definition TR_MALLOC : Z := 0xd20e0.
Definition TR_LLVM : Z := 0x65a88.
Definition TR_EMIT : Z := 0x65a40.
Definition TR_FREE : Z := 0xd1fa0.
Definition TR_MAINRET : Z := 0x6575c.
Definition TR_CALLHEAD : Z := 0x65970.
Definition INITIALIZED : Z := 0xfe4f0.
Definition AEF_CB : Z := 0xfe4f4.
Definition AT_SLOT : Z := 0x120708.
Definition AT_HEAD : Z := 0x120710.
Definition AT_BUILTIN : Z := 0x120718.
Definition AT_F1 : Z := 0x120728.
Definition AT_A1 : Z := 0x120828.
Definition AT_CALL : Z := 0xd00a8.
Definition AEF_GUARD : Z := 0x65a10.
Definition NEED_LOCKS : Z := 0x12094b.
Definition NEW_HANDLER : Z := 0xfe520.
Definition OOM_SPIN : Z := 0.
Definition EMPTY : Z := 0xfe500.
Definition tr_stops : list Z := [TR_POSTINIT; TR_MALLOC; TR_CALLHEAD; TR_LLVM; TR_EMIT; TR_FREE; TR_MAINRET].

Definition tr_sr : list expr :=
  Eval cbv in (map (fun i => match i with
     | 0 => ELit 0 | 1 => ELit TR_MAINRET | 2 => EAlu ALU_ADD (EVar 0) (ELit (-128)) | 3 => ELit 0x10800 | 4 => ELit 0x1006b8
     | 10 => EVar 1 | 11 => EVar 2 | 12 => EVar 3 | 13 => EVar 4
     | _ => EVar (6 + i) end)%nat (seq 0 32)).

Definition tr_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KImg 0x10000 0xee000; KImg 0xfe4e9 0xfe790;
   KWr (SA (ELit 0) 0xee000) 0x34000;
   KWord (SA (ELit 0) NEED_LOCKS) 1 (ELit 0); KImg 0x120700 0x120708; KImg AT_BUILTIN 0x120720;
   KWord (SA (ELit 0) AT_SLOT) 4 (ELit 1); KWord (SA (ELit 0) AT_HEAD) 8 (ELit AT_BUILTIN);
   KRange (EVar 2) 0 32767; KRange (EVar 4) 0 67108863;
   KWord (SA (EVar 1) 0) 1 (EVar 5); KRange (EVar 5) 0 255; KRange (EVar 1) 0x122000 0x7fffff800000;
   KDisj (SA (EVar 1) 0) 1 (SA (EVar 0) (-8388608)) 8388608].

Definition runI := sym_exec RSEGS 3000 true tr_stops (SCR [] [] []) (SS TR_ENTRY tr_sr [] tr_kn 40) [].
Definition ssI := Eval vm_compute in fst (fst runI).
Definition scrI := Eval vm_compute in snd runI.
Lemma rI_eq : sym_exec RSEGS 3000 true tr_stops (SCR [] [] []) (SS TR_ENTRY tr_sr [] tr_kn 40) [] = (ssI, [], scrI).
Proof. vm_compute. reflexivity. Qed.
Lemma rI_pc : s_pc ssI = TR_POSTINIT. Proof. reflexivity. Qed.
Definition srJ := Eval vm_compute in s_regs ssI.
Definition knJ := Eval vm_compute in fst (fst (carry (s_log ssI) tr_kn [])).
Definition hsJ := Eval vm_compute in snd (carry (s_log ssI) tr_kn []).
Lemma cJ_eq : carry (s_log ssI) tr_kn [] = (knJ, [], hsJ). Proof. vm_compute. reflexivity. Qed.

Definition runC (d1 d2 : bool) := sym_exec RSEGS 3000 true tr_stops (SCR [d1; d2] [] []) (SS TR_POSTINIT srJ [] knJ 40) [].
Definition ssC (d1 d2 : bool) := fst (fst (runC d1 d2)).

Definition ssC_tt := Eval vm_compute in ssC true true.
Definition ssC_tf := Eval vm_compute in ssC true false.
Definition ssC_ft := Eval vm_compute in ssC false true.
Definition ssC_ff := Eval vm_compute in ssC false false.
Definition scsC_tt := Eval vm_compute in snd (fst (runC true true)).
Definition scsC_tf := Eval vm_compute in snd (fst (runC true false)).
Definition scsC_ft := Eval vm_compute in snd (fst (runC false true)).
Definition scsC_ff := Eval vm_compute in snd (fst (runC false false)).
Lemma rC_tt_eq : sym_exec RSEGS 3000 true tr_stops (SCR [true; true] [] []) (SS TR_POSTINIT srJ [] knJ 40) [] = (ssC_tt, scsC_tt, snd (runC true true)).
Proof. vm_compute. reflexivity. Qed.
Lemma rC_tf_eq : sym_exec RSEGS 3000 true tr_stops (SCR [true; false] [] []) (SS TR_POSTINIT srJ [] knJ 40) [] = (ssC_tf, scsC_tf, snd (runC true false)).
Proof. vm_compute. reflexivity. Qed.
Lemma rC_ft_eq : sym_exec RSEGS 3000 true tr_stops (SCR [false; true] [] []) (SS TR_POSTINIT srJ [] knJ 40) [] = (ssC_ft, scsC_ft, snd (runC false true)).
Proof. vm_compute. reflexivity. Qed.
Lemma rC_ff_eq : sym_exec RSEGS 3000 true tr_stops (SCR [false; false] [] []) (SS TR_POSTINIT srJ [] knJ 40) [] = (ssC_ff, scsC_ff, snd (runC false false)).
Proof. vm_compute. reflexivity. Qed.

Lemma rC_tt_pc : s_pc ssC_tt = TR_MALLOC. Proof. reflexivity. Qed.
Lemma rC_tf_pc : s_pc ssC_tf = TR_CALLHEAD. Proof. reflexivity. Qed.
Lemma rC_ft_pc : s_pc ssC_ft = TR_CALLHEAD. Proof. reflexivity. Qed.
Lemma rC_ff_pc : s_pc ssC_ff = TR_MALLOC. Proof. reflexivity. Qed.
Lemma rC_tt_log : s_log ssC_tt = []. Proof. reflexivity. Qed.
Lemma rC_tf_log : s_log ssC_tf = []. Proof. reflexivity. Qed.
Lemma rC_ft_log : s_log ssC_ft = []. Proof. reflexivity. Qed.
Lemma rC_ff_log : s_log ssC_ff = []. Proof. reflexivity. Qed.

Definition tr_regions : list sregion :=
  [(SA (EVar 0) (-256), 128); (SA (ELit 0) INITIALIZED, 1); (SA (ELit 0) AT_SLOT, 4); (SA (ELit 0) AT_F1, 8); (SA (ELit 0) AT_A1, 8)].
Lemma rI_cov : log_covered tr_regions (s_log ssI) = true. Proof. vm_compute. reflexivity. Qed.
End FX.
