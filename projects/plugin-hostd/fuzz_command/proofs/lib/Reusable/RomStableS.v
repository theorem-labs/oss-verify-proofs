(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 08b1429): [RomStableK]'s lift for the spin walks ([YK18.srealizes]).
   As G5-8's cgif [Cfg/RomStable.v] ([srealizes_wrom], [srealizes_app_tail], [srun_init]); kept apart
   from [RomStableK] so that [Agree.v] does not wait on [YK18]'s imports. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YK15 YK18.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import RomBase RomStableK.
Import ListNotations.

Section Seg.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Theorem srealizes_wrom : forall c T, YK18.srealizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> YK18.srealizes segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c Hspin Hh | c T T' H IH Heq];
    intros r Hr.
  - apply (YK18.srz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + eapply node_wrom; eauto.
    + intros i. apply IH. erewrite node_rom; eauto.
  - apply YK18.srz_halt. exact Hh.
  - destruct Hspin as [[] _].
  - eapply YK18.srz_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Seg.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem srealizes_app_tail : forall c T,
    YK18.srealizes segs c T -> YK18.srealizes (segs ++ tail) c T.
  Proof.
    intros c T H;
      induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq].
    - apply (YK18.srz_node (segs ++ tail) c I evs nx T i0); [| exact IH].
      eapply node_ok_app_tail; eauto.
    - exact (YK18.srz_halt (segs ++ tail) c Hh).
    - destruct Hspin as [[] _].
    - exact (YK18.srz_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End AppTail.

Theorem srun_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  YK18.srealizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  YK18.srealizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite init_config_run_segments. unfold run_segments at 1.
  apply srealizes_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi |].
  apply (srealizes_wrom segs Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.
