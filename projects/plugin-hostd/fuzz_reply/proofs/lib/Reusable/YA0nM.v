(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YA0nM.v, with its module paths changed. *)
(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YA0nM.v, sha256 070edf335e6160f2766392e092a1c6d69205dc440bfe1c1bc98ef4e9344ca4ca (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* The step and chain twins, additive (no existing text changed). YA0n.SRr_step / SRr_msteps hand the continuation SOME model' with the
   same non-materialized fields (same_but_materialized) and forget the engine's accounting equation
   (YK04.node_instr_restricted's mi_account_step conjunct). The twins here keep it: the continuation also learns that
   model' is materialize_model_accesses of the step's accessed ranges (SRr_stepM), and over a chain of steps that every
   page materialized at the end was materialized at the start or is a page of one of the chain's accesses
   (SRr_mstepsM, mat_in). With YK04M.materialize_adds_only that is the per-step inclusion the lazy-residue argument
   needs (YGcfLazyResid.step_mat_in_cf), once the walk shows the accesses lie in the canonical base. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0n YK0i YK15 YK0j YK18 YK0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YK05 YA0i YA0n YK0x YK04M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

(* A page of one of the accesses accs: the page base of byte k of an access (a, n), k < n. *)
Definition acc_page (accs : list (word * nat)) (p : word) : Prop :=
  exists a n k, In (a, n) accs /\ (k < n)%nat /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.

(* Every page materialized in md' was materialized in md or is a page of the accesses accs. *)
Definition mat_in (md md' : Model) (accs : list (word * nat)) : Prop :=
  forall p, In p (m_vm_materialized md') -> In p (m_vm_materialized md) \/ acc_page accs p.

Lemma acc_page_app_l : forall a1 a2 p, acc_page a1 p -> acc_page (a1 ++ a2) p.
Proof. intros a1 a2 p (a & n & k & Hin & Hk & Hp). exists a, n, k. split; [apply in_or_app; left; exact Hin | auto]. Qed.
Lemma acc_page_app_r : forall a1 a2 p, acc_page a2 p -> acc_page (a1 ++ a2) p.
Proof. intros a1 a2 p (a & n & k & Hin & Hk & Hp). exists a, n, k. split; [apply in_or_app; right; exact Hin | auto]. Qed.

Lemma mat_in_refl : forall md, mat_in md md [].
Proof. intros md p Hp. left. exact Hp. Qed.

Lemma mat_in_trans : forall md1 md2 md3 a1 a2, mat_in md1 md2 a1 -> mat_in md2 md3 a2 -> mat_in md1 md3 (a1 ++ a2).
Proof.
  intros md1 md2 md3 a1 a2 H1 H2 p Hp. destruct (H2 p Hp) as [Hp2 | Hp2].
  - destruct (H1 p Hp2) as [Hp1 | Hp1]; [left; exact Hp1 | right; exact (acc_page_app_l _ _ _ Hp1)].
  - right. exact (acc_page_app_r _ _ _ Hp2).
Qed.

Lemma mat_in_of_materialize : forall md accs md',
  materialize_model_accesses md accs = Some md' -> mat_in md md' accs.
Proof.
  intros md accs md' Hm p Hp. destruct (materialize_mat_adds_acc md accs md' Hm p Hp) as [H | H]; [left | right]; exact H.
Qed.

(* The step of the restricted machine and its access report. *)
Lemma step_report : forall segs ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' ->
  exists rs, step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs).
Proof.
  intros segs ms ms' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs ms) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as <-. exists rs. reflexivity.
Qed.

Lemma report_step : forall segs ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  RiscvSemantics.step segs ms = MachineOk ms'.
Proof. intros segs ms ms' rs Hs. unfold RiscvSemantics.step, drop_access_report. rewrite Hs. reflexivity. Qed.

Section h.
Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* node_instr_restricted, keeping the accounting equation: model' is materialize_model_accesses of the restricted
   step's accessed ranges (the unrestricted step accesses the same ranges, YK04.step_accesses_restrict). *)
Theorem node_instr_restricted_mat : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists model',
    MInv A model' /\ same_but_materialized model model' /\ hclean H msr'
    /\ mi_account_step segs ms model = MachineOk (unrestrict H (ms_mem ms) msr', model')
    /\ (forall rs, step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ msr' rs) ->
          materialize_model_accesses model rs = Some model')
    /\ node_ok segs (mkCfg ms model) unit (fun _ => [])
         (fun _ => mkCfg (unrestrict H (ms_mem ms) msr') model').
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (node_instr_restricted segs H HH Hwx A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & Hcl & Hacc & Hnode).
  exists model'. split; [exact Hinv'|]. split; [exact Hsame|]. split; [exact Hcl|]. split; [exact Hacc|].
  split; [|exact Hnode].
  intros rs Hr.
  destruct (step_accesses_restrict segs H HH Hwx ms msr' rs Hr) as (Hfull & Hrs & _).
  destruct (materialize_restricted H A model rs Hcov Hwf Hinv Hrs) as (mat' & Hmat & _).
  assert (E : mi_account_step segs ms model
              = MachineOk (unrestrict H (ms_mem ms) msr', with_vm_backing (m_vm_lazy model) mat' model)).
  { unfold mi_account_step. rewrite Hfull. cbn [access_value accessed_ranges]. rewrite Hmat. reflexivity. }
  rewrite Hacc in E. injection E as E. rewrite E. exact Hmat.
Qed.
End h.

Section d. Context {fx : YK11.FPState}.
Section e.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.

(* SRr_step, keeping the accounting equation and hclean. *)
Lemma SRr_stepM : forall W ms msr' model Q,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
  (forall model', same_but_materialized model model' -> hclean (w_H W) msr' ->
     (forall rs, step_accesses segs (restrict (w_H W) ms) = MachineOk (@mkAccessReport _ msr' rs) ->
        materialize_model_accesses model rs = Some model') ->
     SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W ms msr' model Q Hsvc Hs Hk HI T HK.
  destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
  destruct (node_instr_restricted_mat segs (w_H W) HH Hwx (w_A W) ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & Hcl & _ & Hmat & Hnode).
  apply (srz_silent1 segs _ _ T Hnode).
  apply (Hk model' Hsame Hcl Hmat).
  - apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
  - exact HK.
Qed.

(* SRr_msteps over a chain with its access report (YK0x.msteps_acc): the continuation learns mat_in. *)
Lemma SRr_mstepsM : forall W msr0 msr' accs,
  msteps_acc segs msr0 msr' accs ->
  forall ms model Q,
  msr0 = restrict (w_H W) ms ->
  (forall model', same_but_materialized model model' -> hclean (w_H W) msr' -> mat_in model model' accs ->
     SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
  SRr segs W (mkCfg ms model) Q.
Proof.
  intros W msr0 msr' accs Hms.
  induction Hms as [msr | msr msr1 msr2 ranges accs Hsvc Hstep Hrest IH]; intros ms model Q -> Hk.
  - specialize (Hk model (same_but_materialized_refl model) (restrict_hclean (w_H W) ms) (mat_in_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    apply (SRr_stepM W ms msr1 model Q Hsvc (report_step segs _ _ _ Hstep)).
    intros model1 Hsame1 Hcl1 Hmat1.
    pose proof (mat_in_of_materialize model ranges model1 (Hmat1 ranges Hstep)) as M1.
    apply (IH (unrestrict (w_H W) (ms_mem ms) msr1) model1 Q).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + intros model' Hsame' Hcl' M2.
      rewrite unrestrict_mem, (unrestrict_munrestrict (w_H W)).
      apply Hk; [exact (same_but_materialized_trans _ _ _ Hsame1 Hsame') | exact Hcl' | exact (mat_in_trans _ _ _ _ _ M1 M2)].
Qed.

(* A restricted msteps chain has an access report (each step's report, YK0x.msteps_acc). *)
Lemma msteps_acc_of_msteps : forall ms ms', msteps segs ms ms' -> exists accs, msteps_acc segs ms ms' accs.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest [accs IH]].
  - exists []. apply msta_refl.
  - destruct (step_report segs ms ms1 Hstep) as [rs Hr]. exists (rs ++ accs). eapply msta_step; eassumption.
Qed.

Lemma msteps_of_msteps_acc : forall ms ms' accs, msteps_acc segs ms ms' accs -> msteps segs ms ms'.
Proof.
  intros ms ms' accs Hms. induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hrest IH].
  - apply mst_refl.
  - eapply mst_step; [exact Hsvc | exact (report_step segs _ _ _ Hstep) | exact IH].
Qed.
End e.
End d.
