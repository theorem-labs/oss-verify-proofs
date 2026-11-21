(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK05.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YK05.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK15.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.BudgetWit.AW Require Import YK18_w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section a.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.
Theorem srz_msteps_restricted0 : forall A msr0 msr',
msteps segs msr0 msr' ->
forall ms model T,
msr0 = restrict H ms ->
lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
m_halted model = None ->
(forall model', MInv A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
srealizes segs (mkCfg ms model) T.
Proof.
intros A msr0 msr' Hms.
induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
intros ms model T -> Hcov Hwf Hinv Hh Hk.
- specialize (Hk model Hinv (same_but_materialized_refl model)).
rewrite unrestrict_restrict in Hk. exact Hk.
- rewrite restrict_svc_pending in Hsvc.
destruct (node_instr_restricted segs H HH Hwx A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
apply (srz_silent1 segs _ _ T Hnode (bnode_none segs ms model Hsvc)).
pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
apply (IH (unrestrict H (ms_mem ms) msr1) model1 T).
+ symmetry. apply restrict_unrestrict_clean. exact Hcl1.
+ replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
+ exact Hwf.
+ exact Hinv1.
+ replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
+ intros model' Hinv' Hsame'.
rewrite unrestrict_mem, unrestrict_munrestrict.
apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
Theorem srz_msteps_restricted_T : forall A ms msr' model T,
lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
m_halted model = None ->
msteps segs (restrict H ms) msr' ->
(forall model',
MInv A model' -> same_but_materialized model model' ->
hclean H msr' ->
srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
srealizes segs (mkCfg ms model) T.
Proof.
intros A ms msr' model T Hcov Hwf Hinv Hh Hms Hk.
assert (Hcl : hclean H msr') by (eapply msteps_hclean; eauto using restrict_hclean).
apply (srz_msteps_restricted0 A (restrict H ms) msr' Hms ms model T eq_refl Hcov Hwf Hinv Hh).
intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.
End a.
