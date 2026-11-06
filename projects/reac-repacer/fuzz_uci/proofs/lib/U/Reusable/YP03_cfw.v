(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP03.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Reusable/YP03.v; 64 of its 116 lines of code are new or changed and 829 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import SlotAgree AgreeLift.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section e.
Variable B : malloc_syms.
Let segs := ms_segs B.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma crz_run_gen : forall n E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok.
intros n E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (sym_run_sound segs tbl tbl_ok _ E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
apply (crealizes_msteps B ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma crz_run_stop : forall n E ss ss' why ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok. intros n E ss ss' why. exact (crz_run_gen n E ss ss' (RS_stopped why)). Qed.
Lemma crz_run_running : forall n E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok. intros n E ss ss'. exact (crz_run_gen n E ss ss' RS_running). Qed.
Lemma crz_run_ecall : forall n E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok. intros n E ss ss'. exact (crz_run_gen n E ss ss' RS_ecall). Qed.
Lemma crz_run_to_gen : forall n stop E ss ss' st ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok.
intros n stop E ss ss' st ms model T Hh Hlz HS Hrun Hk.
destruct (sym_run_to_sound segs tbl tbl_ok _ stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr).
apply (crealizes_msteps B ms ms' model T Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma crz_run_to_stop : forall n stop E ss ss' why ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok. intros n stop E ss ss' why. exact (crz_run_to_gen n stop E ss ss' (RS_stopped why)). Qed.
Lemma crz_run_to_running : forall n stop E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok. intros n stop E ss ss'. exact (crz_run_to_gen n stop E ss ss' RS_running). Qed.
Lemma crz_run_to_ecall : forall n stop E ss ss' ms model T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
crealizes B (mkCfg ms' model) T) ->
crealizes B (mkCfg ms model) T.
Proof using tbl_ok. intros n stop E ss ss'. exact (crz_run_to_gen n stop E ss ss' RS_ecall). Qed.
Lemma crz_branch : forall E ss ms model T c a b,
st_ok segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms ->
crealizes B (mkCfg ms model) T) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
crealizes B (mkCfg ms model) T) ->
crealizes B (mkCfg ms model) T.
Proof using.
intros E ss ms model T c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_ok_add_cond; assumption.
- apply Hf; [reflexivity|]. apply st_ok_add_cond_neg; assumption.
Qed.
End e.
