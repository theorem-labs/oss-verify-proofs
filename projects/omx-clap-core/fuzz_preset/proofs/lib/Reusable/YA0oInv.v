(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, route R1 (a Theorem Labs lane, lane MnPrefix): the table runner of YA0o.v (SRr_run_gen :209,
   SRr_run_to_gen :237, tactics srr_run_with :375 / srr_run_to_with :394) with a memory invariant P carried across the
   run, the form the driver's start-up segments need to bring memnorm from main to the loop head
   (port/mnloop-prefix-leaves.md §3). The invariant is the engine's: P with its laws srr_inv_laws (YC80x.v), and the
   run goes through YC80x.SRr_msteps_inv, exactly as YC80x's own _inv runners do. No local invariant.
   rule 24: no function proved. rule 24: proves no function (kind: runner invariant twin).

   - run_post_inv: YA0o.run_post with the premise P (ms_mem ms') last.
   - SRr_of_restricted_chain_inv / SRr_run_gen_inv / SRr_run_to_gen_inv: YA0o's proofs with SRr_msteps ->
     SRr_msteps_inv and the start premise P (ms_mem ms) after the run equation.
   - Tactics srr_run_with_inv / srr_run_to_with_inv: YA0o's srr_run_with / srr_run_to_with with two more arguments,
     PLAW (srr_inv_laws segs P; P is read from its type) and HPM : P (ms_mem ms); after the run HPM names P of the end
     memory. srr_branch_with needs no twin: a branch does not change the memory, so HPM stays valid.
   Generic in segs and the table, so the A image and the B image use this one file. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK18 YK0j YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Section d.
Variable segs : list Segment.
Context {fx : FPState}.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
(* YA0o.v:182 run_post, with P of the end memory last *)
Definition run_post_inv (W : world segs) (E : env) (ss ss' : sstate) (st : run_status)
(ms : machine_state) (model : Model) (Q : world segs -> config -> Prop) : Prop :=
forall ms' mat',
match st with RS_ecall => st_ok_ecall segs E ss' (restrict (w_H W) ms')
| _ => st_ok segs E ss' (restrict (w_H W) ms') end ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
P (ms_mem ms') ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q.
(* YA0o.v:190 SRr_of_restricted_chain; SRr_msteps -> SRr_msteps_inv *)
Lemma SRr_of_restricted_chain_inv : forall W E ss ss' st ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
match st with RS_ecall => st_ok_ecall segs E ss' msr' | _ => st_ok segs E ss' msr' end ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
P (ms_mem ms) ->
run_post_inv W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W E ss ss' st ms msr' model Q Hms HS' Hfr HPm Hk.
apply (SRr_msteps_inv segs Hwx P PLAW W ms msr' model Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))).
rewrite Hrr. exact Hfr.
- exact HPm'.
Qed.
(* YA0o.v:209 SRr_run_gen *)
Lemma SRr_run_gen_inv : forall W n E ss ss' st ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_runN segs tbl n ss = (ss', st) ->
P (ms_mem ms) ->
run_post_inv W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun HPm Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chain_inv W E ss ss' st ms msr' model Q Hms HS' Hfr HPm Hk).
Qed.
(* YA0o.v:237 SRr_run_to_gen *)
Lemma SRr_run_to_gen_inv : forall W n stop E ss ss' st ms model Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sym_run_toN segs tbl n stop ss = (ss', st) ->
P (ms_mem ms) ->
run_post_inv W E ss ss' st ms model Q ->
SRr segs W (mkCfg ms model) Q.
Proof.
intros W n stop E ss ss' st ms model Q HS Hrun HPm Hk.
destruct (msteps_run_to_gen segs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chain_inv W E ss ss' st ms msr' model Q Hms HS' Hfr HPm Hk).
Qed.
End d.

(* YA0o.v:364 srr_after_run, introducing the end memory's P as HPM *)
Ltac srr_after_run_inv HS HPM :=
let ms' := fresh "ms" in let mat' := fresh "mat" in
let HF := fresh "HF" in let HFr := fresh "HFr" in
intros ms' mat' HS HF HFr HPM;
cbn [ms_mem mkst pend_at] in HF, HFr, HPM;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
(* YA0o.v:375 srr_run_with; PLAW : srr_inv_laws segs P, HPM : P (ms_mem ms) *)
Ltac srr_run_with_inv tblok PLAW HS HPM :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
lazymatch type of PLAW with
| srr_inv_laws _ ?P =>
let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_with_inv: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_gen_inv segs tbl tblok HWX P PLAW W FUEL E ss ss' st ms _ _ HS Hrun HPM);
clear Hrun HS HPM;
srr_after_run_inv HS HPM
end
| _ => fail "srr_run_with_inv: PLAW must be  srr_inv_laws segs P"
end
end
| _ => fail "srr_run_with_inv: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.
(* YA0o.v:394 srr_run_to_with *)
Ltac srr_run_to_with_inv tblok PLAW HS HPM stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
lazymatch type of PLAW with
| srr_inv_laws _ ?P =>
let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX
| _ => fail "srr_run_to_with_inv: no hypothesis  wx_segs_nowrap segs" end in
eapply (SRr_run_to_gen_inv segs tbl tblok HWX P PLAW W FUEL stop E ss ss' st ms _ _ HS Hrun HPM);
clear Hrun HS HPM;
cbv beta iota;
srr_after_run_inv HS HPM
end
| _ => fail "srr_run_to_with_inv: PLAW must be  srr_inv_laws segs P"
end
end
| _ => fail "srr_run_to_with_inv: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
end.

Check SRr_run_gen_inv.
Check SRr_run_to_gen_inv.
Print Assumptions SRr_run_gen_inv.
Print Assumptions SRr_run_to_gen_inv.
