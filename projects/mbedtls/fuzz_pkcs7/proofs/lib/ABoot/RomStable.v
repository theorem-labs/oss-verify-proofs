(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: its provenance comment names its source by unit and file. *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): an [ABoot.SpinAlg.srealizes] walk over a binary's own
   segments, lifted to the run's ([run_segments]) from the run's own start ([srun_init]).

   Why it is needed: at the revision the run reads the image through
   ms_rom = seg_rom (run_segments ..), a larger backing than the binary's own segments, and
   [sys_input] reads memory through ms_rom; so a walk over [segs] lifts to the run only because
   each syscall node answers the same on the larger backing - [RomBase.sys_rob], node_ok's third
   conjunct.  The step-level facts are [Common/Cfg/RomStep.v].

   Donor (proof shape): the double-conversion/string_to_double_fuzzer unit's
   RomStable.v:110-112, 184-193,
   221-242, 488-533, 603-612, 655-666, adapted (i) to this tree's node_ok conjunct and (ii) to
   this tree's [srealizes], whose excused-node constructor [srz_node_sp] carries
   [~ fo_step c (evs i) (nx i)]: that side condition moves along both lifts by the forced-only
   back-steps [RomStep.sstep_cfg_wrom_back] / [RomStep.sstep_cfg_app_back]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require Import RomBase RomStep.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ShapeAlg DivergeSim SpinAlg.
Import ListNotations.

Section Seg.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.

Lemma node_rom : forall c I evs nx, node_ok segs c I evs nx ->
  forall i, ms_rom (cfg_ms (nx i)) = ms_rom (cfg_ms c).
Proof. intros c I evs nx [Hc _] i. exact (sstep_next_rom segs Hvi _ _ _ (Hc i)). Qed.

Lemma node_wrom : forall c I evs nx r,
  node_ok segs c I evs nx -> rom_ext (ms_rom (cfg_ms c)) r ->
  node_ok segs (cwrom c r) I evs (fun i => cwrom (nx i) r).
Proof.
  intros c I evs nx r [Hc [Hb Hrob]] Hr. split; [|split].
  - intros i. exact (sstep_wrom_fwd segs Hvi c (evs i) (nx i) r Hrob Hr (Hc i)).
  - intros e st Hst.
    destruct (sstep_wrom_back segs Hvi c e st r Hrob Hr Hst) as (st0 & H0 & ->).
    destruct (Hb e st0 H0) as (i & -> & ->). exists i. split; reflexivity.
  - exact (sys_rob_wrom segs c r Hrob Hr).
Qed.

(** An excused successor stays excused at the larger backing. *)
Lemma nfo_wrom : forall c I evs nx r i,
  node_ok segs c I evs nx -> rom_ext (ms_rom (cfg_ms c)) r ->
  ~ fo_step segs c (evs i) (nx i) -> ~ fo_step segs (cwrom c r) (evs i) (cwrom (nx i) r).
Proof.
  intros c I evs nx r i Hn Hr Hnf Hf. unfold fo_step in Hf.
  destruct Hn as [Hc [Hb Hrob]].
  destruct (sstep_cfg_wrom_back segs Hvi c (evs i) _ r Hrob Hr Hf) as ([c0|] & H0 & E);
    [| discriminate E].
  assert (E' : cwrom c0 r = cwrom (nx i) r) by congruence.
  assert (Hr0 : ms_rom (cfg_ms c0) = ms_rom (cfg_ms (nx i))).
  { rewrite (sstep_cfg_next_rom segs Hvi _ _ _ H0).
    symmetry. exact (sstep_next_rom segs Hvi _ _ _ (Hc i)). }
  pose proof (cwrom_inj c0 (nx i) r Hr0 E') as ->.
  apply Hnf. exact H0.
Qed.

Lemma to_spin_wrom : forall ms model r, to_spin segs ms model -> to_spin segs (wrom ms r) model.
Proof.
  intros ms model r H.
  induction H as [ms model Hs Hm | ms model ms' model' Hs Hm H IH].
  - apply ts_spin; [exact Hs |]. rewrite mi_account_step_wrom, Hm. reflexivity.
  - eapply ts_step; [exact Hs | | exact IH].
    rewrite mi_account_step_wrom, Hm. reflexivity.
Qed.

Theorem srealizes0_wrom : forall c T, srealizes0 segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizes0 segs (cwrom c r) T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c Hspin Hh | c T T' H IH Heq];
    intros r Hr.
  - apply (srz0_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hr).
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - apply srz0_halt. exact Hh.
  - apply srz0_spin; [exact (to_spin_wrom _ _ r Hspin) | exact Hh].
  - eapply srz0_conseq; [apply IH; exact Hr | exact Heq].
Qed.

Theorem srealizes_wrom : forall c T, srealizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizes segs (cwrom c r) T.
Proof.
  apply (srealizes_ind2 segs (fun c T => forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizes segs (cwrom c r) T)).
  - intros c I evs nx T i0 Hn _ IH r Hr.
    apply (srz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hr).
    + intros i. apply IH. rewrite (node_rom c I evs nx Hn i). exact Hr.
  - intros c Hh r Hr. apply srz_halt. exact Hh.
  - intros c I evs nx T i0 Hn Hk r Hr.
    apply (srz_node_sp segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom c I evs nx r Hn Hr).
    + intros i. assert (Hri : rom_ext (ms_rom (cfg_ms (nx i))) r)
        by (rewrite (node_rom c I evs nx Hn i); exact Hr).
      destruct (Hk i) as [[_ IH] | [H0 Hnf]].
      * left. exact (IH r Hri).
      * right. split; [exact (srealizes0_wrom _ _ H0 r Hri) | exact (nfo_wrom c I evs nx r i Hn Hr Hnf)].
  - intros c T T' _ IH Heq r Hr. eapply srz_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Seg.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Lemma node_ok_app_tail : forall c (I : Type) evs nx (i0 : I),
    node_ok segs c I evs nx -> node_ok (segs ++ tail) c I evs nx.
  Proof.
    intros [ms model] I evs nx i0 [Hc [Hs Hrob]]. split; [|split].
    - intros i. apply (sstep_app_next segs tail); first [assumption | exact (Hc i)].
    - intros e st Hb. apply Hs. apply (sstep_app_back segs tail); try assumption.
      eapply instr_ok_of_step; first [exact (Hc i0) | eassumption].
    - apply (sys_rob_app_tail segs tail); assumption.
  Qed.

  Lemma nfo_app_tail : forall c (I : Type) evs nx (i0 : I) i,
    node_ok segs c I evs nx ->
    ~ fo_step segs c (evs i) (nx i) -> ~ fo_step (segs ++ tail) c (evs i) (nx i).
  Proof.
    intros [ms model] I evs nx i0 i [Hc _] Hnf Hf. apply Hnf. unfold fo_step in *.
    apply (sstep_cfg_app_back segs tail); try assumption.
    eapply instr_ok_of_step; first [exact (Hc i0) | eassumption].
  Qed.

  Lemma to_spin_app_tail : forall ms model, to_spin segs ms model -> to_spin (segs ++ tail) ms model.
  Proof.
    intros ms model H.
    induction H as [ms model Hs Hm | ms model ms' model' Hs Hm H IH].
    - apply ts_spin; [exact Hs | apply (mi_account_step_app_nx segs tail); assumption].
    - eapply ts_step; [exact Hs | apply (mi_account_step_app_nx segs tail); eassumption | exact IH].
  Qed.

  Theorem srealizes0_app_tail : forall c T, srealizes0 segs c T -> srealizes0 (segs ++ tail) c T.
  Proof.
    intros c T H;
      induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq].
    - exact (srz0_node (segs ++ tail) c I evs nx T i0 (node_ok_app_tail c I evs nx i0 Hnode) IH).
    - exact (srz0_halt (segs ++ tail) c Hh).
    - exact (srz0_spin (segs ++ tail) c (to_spin_app_tail _ _ Hspin) Hh).
    - exact (srz0_conseq (segs ++ tail) c T T' IH Heq).
  Qed.

  Theorem srealizes_app_tail : forall c T, srealizes segs c T -> srealizes (segs ++ tail) c T.
  Proof.
    apply (srealizes_ind2 segs (fun c T => srealizes (segs ++ tail) c T)).
    - intros c I evs nx T i0 Hn _ IH.
      exact (srz_node (segs ++ tail) c I evs nx T i0 (node_ok_app_tail c I evs nx i0 Hn) IH).
    - intros c Hh. exact (srz_halt (segs ++ tail) c Hh).
    - intros c I evs nx T i0 Hn Hk.
      apply (srz_node_sp (segs ++ tail) c I evs nx T i0 (node_ok_app_tail c I evs nx i0 Hn)).
      intros i. destruct (Hk i) as [[_ IH] | [H0 Hnf]].
      + left. exact IH.
      + right. split; [exact (srealizes0_app_tail _ _ H0) | exact (nfo_app_tail c I evs nx i0 i Hn Hnf)].
    - intros c T T' _ IH Heq. exact (srz_conseq (segs ++ tail) c T T' IH Heq).
  Qed.
End AppTail.

Theorem srealizes_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  srealizes segs c T -> srealizes (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply srealizes_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** The supplier-walk bridge for the sanitized walk. *)
Theorem srun_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  srealizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  srealizes (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite init_config_run_segments.
  apply srealizes_run_segments; [exact Hvi|].
  apply (srealizes_wrom segs Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.
