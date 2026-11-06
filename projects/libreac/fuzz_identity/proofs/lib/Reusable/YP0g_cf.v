(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YP0g.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YP0g.v, with its module paths changed; 22 of its 162 lines of code are new or changed and 138 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM06_cf YO0d_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Context {fx : FPState}.
Lemma SR_run_gen : forall n E ss ss' st ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR_cfv segs (mkCfg ms' model) Q) ->
SR_cfv segs (mkCfg ms model) Q.
Proof.
intros n E ss ss' st ms model Q Hh Hlz HS Hrun Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (SR_cfv_msteps segs ms ms' model Q Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma SR_run_stop : forall n E ss ss' why ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_stopped why) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR_cfv segs (mkCfg ms' model) Q) ->
SR_cfv segs (mkCfg ms model) Q.
Proof. intros n E ss ss' why. exact (SR_run_gen n E ss ss' (RS_stopped why)). Qed.
Lemma SR_run_running : forall n E ss ss' ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_running) ->
(forall ms', st_ok segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR_cfv segs (mkCfg ms' model) Q) ->
SR_cfv segs (mkCfg ms model) Q.
Proof. intros n E ss ss'. exact (SR_run_gen n E ss ss' RS_running). Qed.
Lemma SR_run_ecall : forall n E ss ss' ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_runN segs tbl n ss = (ss', RS_ecall) ->
(forall ms', st_ok_ecall segs E ss' ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR_cfv segs (mkCfg ms' model) Q) ->
SR_cfv segs (mkCfg ms model) Q.
Proof. intros n E ss ss'. exact (SR_run_gen n E ss ss' RS_ecall). Qed.
Lemma SR_run_to_gen : forall n stop E ss ss' st ms model Q,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok segs E ss ms ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
(forall ms',
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
SR_cfv segs (mkCfg ms' model) Q) ->
SR_cfv segs (mkCfg ms model) Q.
Proof.
intros n stop E ss ss' st ms model Q Hh Hlz HS Hrun Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & Hfr).
apply (SR_cfv_msteps segs ms ms' model Q Hh Hlz Hms). apply Hk; assumption.
Qed.
Lemma SR_sym_branch : forall E ss ms model Q c a b,
st_ok segs E ss ms ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true ->
st_ok segs E (add_cond ss (mkAC c a b)) ms ->
SR_cfv segs (mkCfg ms model) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false ->
st_ok segs E (add_cond ss (mkAC (neg_bc c) a b)) ms ->
SR_cfv segs (mkCfg ms model) Q) ->
SR_cfv segs (mkCfg ms model) Q.
Proof.
intros E ss ms model Q c a b HS Ht Hf.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply Ht; [reflexivity|]. apply st_ok_add_cond; assumption.
- apply Hf; [reflexivity|]. apply st_ok_add_cond_neg; assumption.
Qed.
Lemma SR_st_ok_ret : forall (Q : config -> Prop) ms model,
Q (mkCfg ms model) -> SR_cfv segs (mkCfg ms model) Q.
Proof. intros Q ms model HQ. apply SR_cfv_ret. exact HQ. Qed.
Lemma t_alt2_idem : forall T, t_eq (t_alt2 T T) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.
Lemma t_alt2_idem3 : forall T, t_eq (t_alt2 T (t_alt2 T T)) T.
Proof. intros T tr. unfold t_alt2. tauto. Qed.
End d.
Ltac sr_run_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
lazymatch st with
| RS_ecall =>
eapply (SR_run_ecall segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport_ecall segs E ss ss' ms' HS HF
| RS_stopped ?why =>
eapply (SR_run_stop segs tbl tblok FUEL E ss ss' why ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
| RS_running =>
eapply (SR_run_running segs tbl tblok FUEL E ss ss' ms);
[ | | exact HS | exact Hrun | clear Hrun HS; intros ms' HS HF ]; [assumption|assumption|];
sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sr_run_to_with tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let ms' := fresh "ms" in let HF := fresh "HF" in
eapply (SR_run_to_gen segs tbl tblok FUEL stop E ss ss' st ms);
[ | | exact HS | exact Hrun | clear Hrun HS; cbv beta iota; intros ms' HS HF ];
[assumption|assumption|];
lazymatch st with
| RS_ecall => sym_transport_ecall segs E ss ss' ms' HS HF
| _ => sym_transport segs E ss ss' ms' HS HF
end
end
end
end.
Ltac sr_branch_with tblok HS :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_why segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (SR_sym_branch segs E ss ms _ _ c a b HS);
clear HS;
let Hc := fresh "Hc" in
intros Hc HS
| _ => fail "sr_branch: state is not stuck at a branch:" why
end
end
end.
