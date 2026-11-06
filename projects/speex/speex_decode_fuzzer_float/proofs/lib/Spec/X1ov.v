(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ri X1r3 X1r6 X1pe X1os.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Section StdioL.
Context {St : Type}.
Variable B : Z.
Variable I : assn St.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Hypothesis I_live : forall s mo, I s mo -> step_live B mo.
Hypothesis I_so : forall v s mo, I s mo -> I (set_so v s) mo.

#[using="I_live"] Lemma stdio_wloop_L : forall fuel fd iovs, mspecL B I (stdio_wloop fuel fd iovs) (fun _ => I).
Proof.
induction fuel as [|fuel IH]; intros fd iovs; cbn [stdio_wloop]; [apply mspecL_munr|].
eapply mspecL_bind with (Q1 := fun _ => I).
- apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s mo HI rsp mo' evs Hst. destruct Hst as [-> _].
split; [exact (I_live _ _ HI)|]. intros a _. exact HI.
- intros cnt. destruct (cnt =? wv_total iovs); [apply mspecL_ret; intros s mo H; exact H| apply IH].
Qed.

#[using="I_live"] Lemma stdio_writev_L : forall fd buf s, mspecL B I (stdio_writev fd buf s) (fun _ => I).
Proof.
intros fd buf s. unfold stdio_writev. destruct (WRITEV_MAX <? _); [apply mspecL_munr| apply stdio_wloop_L].
Qed.

#[using="I_so"] Lemma upd_so_L : forall f, mspecL B I (upd_so get_so set_so f) (fun _ => I).
Proof. intros f. unfold upd_so. apply mspecL_upd'. intros s mo H. apply I_so. exact H. Qed.

#[using="Type"] Lemma rd_so_L : forall (P : assn St), mspecL B P (rd_so get_so) (fun so s mo => P s mo /\ so = get_so s).
Proof.
intros P. unfold rd_so. eapply mspecL_bind; [apply mspecL_get|]. intros s0. apply mspecL_ret.
intros s mo [-> H]. split; [exact H| reflexivity].
Qed.

#[using="I_live I_so"] Lemma stdout_stdio_write_L : forall s, mspecL B I (stdout_stdio_write get_so set_so s) (fun _ => I).
Proof.
intros s. unfold stdout_stdio_write. eapply mspecL_bind; [apply (rd_so_L I)|]. intros so.
eapply mspecL_seq; [eapply mspecL_pre; [apply stdio_writev_L| intros s' mo' [H _]; exact H]|].
intros _. apply upd_so_L.
Qed.

#[using="I_live I_so"] Lemma stdout_writefn_L : forall s, mspecL B I (stdout_writefn get_so set_so s) (fun _ => I).
Proof.
intros s. unfold stdout_writefn. eapply mspecL_bind; [apply (rd_so_L I)|]. intros so.
eapply mspecL_seq with (R := I).
- destruct (so_first so).
+ eapply mspecL_seq; [eapply mspecL_pre; [apply upd_so_L| intros s' mo' [H _]; exact H]|]. intros _.
eapply mspecL_bind with (Q1 := fun _ => I).
* apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s' mo' HI rsp mo'' evs Hst.
destruct (nstep_dec_ioctl 1 TIOCGWINSZ mo' rsp mo'' evs Hst) as (_ & -> & _).
split; [exact (I_live _ _ HI)|]. intros a _. exact HI.
* intros [e|v]; [apply upd_so_L| apply mspecL_munr].
+ apply mspecL_ret. intros s' mo' [H _]. exact H.
- intros _. apply stdout_stdio_write_L.
Qed.

#[using="I_so"] Lemma stdout_towrite_L : mspecL B I (stdout_towrite get_so set_so) (fun _ => I).
Proof. unfold stdout_towrite. apply upd_so_L. Qed.

#[using="I_live I_so"] Lemma stdout_fwritex_L : forall s, mspecL B I (stdout_fwritex get_so set_so s) (fun _ => I).
Proof.
intros s. unfold stdout_fwritex.
eapply mspecL_seq; [apply stdout_towrite_L|]. intros _.
eapply mspecL_bind; [apply (rd_so_L I)|]. intros so.
eapply mspecL_pre with (P := I); [| intros s' mo' [H _]; exact H].
destruct (_ <? _); [apply stdout_writefn_L|].
destruct (so_lbf_nl so); [| apply upd_so_L].
eapply mspecL_seq; [| intros _; apply upd_so_L].
destruct (0 <? _); [apply stdout_writefn_L| apply mspecL_ret; intros s' mo' H; exact H].
Qed.

#[using="I_live I_so"] Lemma out_pieces_L : forall ps, mspecL B I (out_pieces get_so set_so ps) (fun _ => I).
Proof.
induction ps as [|p ps IH]; cbn [out_pieces]; [apply mspecL_ret; intros s mo H; exact H|].
eapply mspecL_seq; [apply stdout_fwritex_L|]. intros _. exact IH.
Qed.

#[using="I_live I_so"] Lemma stdout_vprintf_L : forall ps, mspecL B I (stdout_vprintf get_so set_so ps) (fun _ => I).
Proof. intros ps. unfold stdout_vprintf. eapply mspecL_seq; [apply stdout_towrite_L|]. intros _. apply out_pieces_L. Qed.

#[using="I_live I_so"] Lemma stdout_exit_flush_L : mspecL B I (stdout_exit_flush get_so set_so) (fun _ => I).
Proof.
unfold stdout_exit_flush. eapply mspecL_bind; [apply (rd_so_L I)|]. intros so.
eapply mspecL_pre with (P := I); [| intros s' mo' [H _]; exact H].
destruct (0 <? _); [apply stdout_writefn_L| apply mspecL_ret; intros s mo H; exact H].
Qed.

#[using="I_live"] Lemma stderr_pieces_L : forall ps buf, mspecL B I (stderr_pieces buf ps) (fun _ => I).
Proof.
induction ps as [|p ps IH]; intros buf; cbn [stderr_pieces]; [apply mspecL_ret; intros s mo H; exact H|].
destruct (_ <? _); [| apply IH].
eapply mspecL_seq; [apply stdio_writev_L|]. intros _. apply IH.
Qed.

#[using="I_live"] Lemma stderr_fprintf_L : forall ps, mspecL B I (stderr_fprintf ps) (fun _ => I).
Proof.
intros ps. unfold stderr_fprintf. eapply mspecL_seq; [apply stderr_pieces_L|]. intros buf. apply stdio_writev_L.
Qed.

#[using="I_live"] Lemma stderr_fwrite_L : forall s, mspecL B I (stderr_fwrite s) (fun _ => I).
Proof.
intros s. unfold stderr_fwrite. destruct (0 <? _); [apply stdio_writev_L| apply mspecL_ret; intros s' mo H; exact H].
Qed.

#[using="I_live I_so"] Lemma stdio_exit_model_L : forall code (P : assn St),
(forall s mo, P s mo -> I s mo) ->
mspecL B P (stdio_exit_model get_so set_so code) (fun _ _ _ => False).
Proof.
intros code P HP. unfold stdio_exit_model. eapply mspecL_seq with (R := I).
- eapply mspecL_pre; [apply stdout_exit_flush_L| exact HP].
- intros _. apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s mo _ rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.

#[using="I_live"] Lemma s_diag_L : forall d, mspecL B I (s_diag d) (fun _ => I).
Proof. intros d. unfold s_diag. destruct d; first [apply stderr_fprintf_L | apply stderr_fwrite_L]. Qed.
#[using="I_live I_so"] Lemma s_emit_L : forall rc, mspecL B I (s_emit get_so set_so rc) (fun _ => I).
Proof. intros rc. unfold s_emit. apply stdout_vprintf_L. Qed.
#[using="I_live"] Lemma s_notify_L : forall m, mspecL B I (s_notify m) (fun _ => I).
Proof. intros m. unfold s_notify. apply stderr_fprintf_L. Qed.
#[using="I_live"] Lemma s_warning_L : forall m, mspecL B I (s_warning m) (fun _ => I).
Proof. intros m. unfold s_warning. apply stderr_fprintf_L. Qed.
End StdioL.

Section ProgIOL.
Variable B : Z.
Variable I : assn PState.
Hypothesis I_live : forall s mo, I s mo -> step_live B mo.
Hypothesis I_so : forall v s mo, I s mo -> I (set_so_ps v s) mo.
Hypothesis I_minv : forall s mo, I s mo -> minv mo /\ m_halted mo = None.
Hypothesis I_vm : forall s mo mo', I s mo -> m_vm mo' = m_vm mo -> minv mo' -> m_halted mo' = None -> I s mo'.

#[using="I_live"] Lemma io_diag_L : forall d, mspecL B I (io_diag d) (fun _ => I).
Proof. intros d. unfold io_diag. apply s_diag_L; assumption. Qed.
#[using="I_live I_so"] Lemma io_emit_L : forall rc, mspecL B I (io_emit rc) (fun _ => I).
Proof. intros rc. unfold io_emit. apply s_emit_L; assumption. Qed.
#[using="I_live"] Lemma io_notify_L : forall m, mspecL B I (io_notify m) (fun _ => I).
Proof. intros m. unfold io_notify. apply s_notify_L; assumption. Qed.
#[using="I_live"] Lemma io_warning_L : forall m, mspecL B I (io_warning m) (fun _ => I).
Proof. intros m. unfold io_warning. apply s_warning_L; assumption. Qed.
#[using="I_live I_so"] Lemma io_exit_L : forall code (P : assn PState), (forall s mo, P s mo -> I s mo) ->
mspecL B P (io_exit code) (fun _ _ _ => False).
Proof. intros code P HP. unfold io_exit. apply (stdio_exit_model_L B I ps_so set_so_ps I_live I_so code P HP). Qed.

#[using="Type"] Lemma m_vm_with_tid' v m : m_vm (with_tid v m) = m_vm m.
Proof. destruct m; reflexivity. Qed.

#[using="I_live I_minv I_vm"] Lemma startup_L : mspecL B I startup (fun _ => I).
Proof.
unfold startup. eapply mspecL_seq; [| intros _; apply mspecL_ret; intros s mo H; exact H].
apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s mo HI rsp mo' evs Hst.
destruct (I_minv _ _ HI) as [Hmi Hh].
pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
destruct (minv_preserved NSetTid mo rsp mo' evs Logic.I Hmi Hh Hst) as [Hh' Hmi'].
assert (Hvm : m_vm mo' = m_vm mo) by (destruct Hmo as [[_ ->]|[_ ->]]; [reflexivity| apply m_vm_with_tid']).
assert (HI' : I s mo') by (eapply I_vm; eauto).
split; [exact (I_live _ _ HI')|]. intros a _. exact HI'.
Qed.
End ProgIOL.
