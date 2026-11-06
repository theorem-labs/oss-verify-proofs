From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Exec ExecF.
Import ListNotations.

(* Every lib.Lib Exec run is a footprint run under RNG_all. Use: re-derive an old lemma whose premises are
   evt continuations (CPS form) from its <lemma>_F at RNG_all: map each continuation with evt_evtF_all, then
   conclude with evtF_evt. *)

Section WithSegs.
Variable segs : list Segment.

Lemma mstep_mstepF_all : forall ms ms', mstep segs ms ms' -> mstepF segs RNG_all ms ms'.
Proof.
  intros ms ms' [Hs Hstep]. split; [exact Hs|].
  pose proof (RiscvSemantics.drop_step_accesses segs ms) as Hdrop.
  destruct (RiscvSemantics.step_accesses segs ms) as [report| |] eqn:Hacc; cbn in Hdrop;
    rewrite Hstep in Hdrop; try discriminate.
  injection Hdrop as Hv. destruct report as [v accs]. cbn in Hv. subst v.
  exists accs. split; [reflexivity|]. apply Forall_forall. intros x _. exact I.
Qed.

Lemma msteps_mstepsF_all : forall ms ms', msteps segs ms ms' -> mstepsF segs RNG_all ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 H1 _ IH]; [constructor|].
  econstructor; [apply mstep_mstepF_all; exact H1 | exact IH].
Qed.

Lemma evt_evtF_all : forall Q ms, evt segs Q ms -> evtF segs RNG_all Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [apply msteps_mstepsF_all; exact H | exact HQ].
Qed.

(* The two directions together: at RNG_all the footprint run and the plain run are the same. *)
Lemma evtF_all_iff : forall Q ms, evtF segs RNG_all Q ms <-> evt segs Q ms.
Proof. intros Q ms. split; [apply evtF_evt | apply evt_evtF_all]. Qed.

End WithSegs.
