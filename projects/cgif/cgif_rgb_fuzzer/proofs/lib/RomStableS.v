(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the [YK18.srealizesE] half of the run-segments bridge
   of [RomStable]: a walk over a binary's own segments, from the binary's start, lifted to the
   run's segment list from the run's start ([srun_initE]).  [srealizesE] has one constructor
   more than [YK15.realizes], [srzE_spin] ([YK0k.to_spin]); [to_spin_wrom] (by
   [RomStable.mi_account_step_wrom]) and [to_spin_app_tail] (by
   [RomStable.mi_account_step_app_nx]) carry it, as the spin leaf of the srealizes variant of
   leptonica's and bzip2's [SRomStable.v] does.  Every node case is [RomStable]'s. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YK0k YK18 RomBase RomStable.
Import ListNotations.
Local Open Scope Z_scope.

Section Seg.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Lemma to_spin_wrom : forall ms model r, to_spin segs ms model -> to_spin segs (wrom ms r) model.
Proof.
  intros ms model r H.
  induction H as [ms model Hs Hm | ms model ms' model' Hs Hm H IH].
  - apply ts_spin; [exact Hs |]. rewrite mi_account_step_wrom, Hm. reflexivity.
  - eapply ts_step; [exact Hs | | exact IH].
    rewrite mi_account_step_wrom, Hm. reflexivity.
Qed.

Theorem srealizesE_wrom : forall c T, srealizesE segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizesE segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c Hspin Hh | c T T' H IH Heq];
    intros r Hr.
  - apply (srzE_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom segs Hvi c I evs nx r Hn Hr).
    + intros i. apply IH. rewrite (node_rom segs Hvi c I evs nx Hn i). exact Hr.
  - apply srzE_halt. exact Hh.
  - apply srzE_spin; [exact (to_spin_wrom _ _ r Hspin) | exact Hh].
  - eapply srzE_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Seg.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Lemma to_spin_app_tail : forall ms model, to_spin segs ms model -> to_spin (segs ++ tail) ms model.
  Proof.
    intros ms model H.
    induction H as [ms model Hs Hm | ms model ms' model' Hs Hm H IH].
    - apply ts_spin; [exact Hs |]. apply (mi_account_step_app_nx segs tail); assumption.
    - eapply ts_step; [exact Hs | apply (mi_account_step_app_nx segs tail); eassumption | exact IH].
  Qed.

  Theorem srealizesE_app_tail : forall c T, srealizesE segs c T -> srealizesE (segs ++ tail) c T.
  Proof.
    intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq].
    - exact (srzE_node (segs ++ tail) c I evs nx T i0
               (node_ok_app_tail segs tail Hnx Hnw Hvi c I evs nx i0 Hnode) IH).
    - exact (srzE_halt (segs ++ tail) c Hh).
    - exact (srzE_spin (segs ++ tail) c (to_spin_app_tail _ _ Hspin) Hh).
    - exact (srzE_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End AppTail.

Theorem srealizesE_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  srealizesE segs c T -> srealizesE (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply srealizesE_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** A walk over the binary's own segments, from the binary's start, is one over the run's,
    from the run's start. *)
Theorem srun_initE : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  srealizesE segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  srealizesE (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite init_config_run_segments.
  apply srealizesE_run_segments; [exact Hvi|].
  apply (srealizesE_wrom segs Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.
