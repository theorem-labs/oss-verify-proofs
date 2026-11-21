(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the ASan walks ([AS.SpinAlg.srealizes]) over the binary's own
   segments, lifted to the run, as [RomStable.run_init] lifts [ShapeAlg.realizes].

   [srealizes] is [ShapeAlg.realizes] over the same filtered step ([sstep_cfg] at [ACFG]) with one more
   leaf, [srz_sloop]: a [DivergeSim.silent_loop] set of configurations.  Its nodes transfer with
   [RomStable]'s Part 1-2 lemmas (the two relations' [node_ok] are the same predicate); the leaf
   transfers because [silent_loop] reads the state only through [mi_account_step], which does not
   read [ms_rom] ([RomStable.mi_account_step_wrom]) and answers the same over a longer list whose tail
   is neither executable nor writable ([RomStable.mi_account_step_app_nx]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RomBase RomStable.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import ShapeAlg DivergeSim SpinAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation rnode_ok := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.node_ok.

(** * A larger read-only backing *)
Section Seg.
Variable segs : list Segment.

Definition loop_wrom (P : config -> Prop) : config -> Prop :=
  fun c' => exists c r, P c /\ rom_ext (ms_rom (cfg_ms c)) r /\ c' = cwrom c r.

Lemma silent_loop_wrom : forall P, silent_loop segs P -> silent_loop segs (loop_wrom P).
Proof.
  intros P Hl c' (c & r & HP & Hr & ->).
  destruct (Hl c HP) as (Hh & Hsvc & ms' & m' & Hacc & HP').
  destruct c as [ms m]. cbn [cfg_ms cfg_model] in *. unfold cwrom. cbn [cfg_ms cfg_model].
  split; [exact Hh|]. split; [exact Hsvc|].
  exists (wrom ms' r), m'. split.
  - rewrite (mi_account_step_wrom segs ms m r), Hacc. reflexivity.
  - exists (mkCfg ms' m'), r. split; [exact HP'|]. split; [| reflexivity].
    cbn [cfg_ms]. rewrite (mi_account_step_rom segs _ _ _ _ Hacc). exact Hr.
Qed.

Hypothesis Hvi : vdso_image segs = None.

Theorem srealizes_wrom : forall c T, srealizes segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> srealizes segs (cwrom c r) T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hn Hrob Hc IH | c Hh | c P Hl HP | c T T' H IH Heq];
    intros r Hr.
  - apply (srz_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + exact (node_wrom segs Hvi c I evs nx r Hn Hrob Hr).
    + exact (sys_rob_wrom segs c r Hrob Hr).
    + intros i. apply IH. rewrite (node_rom segs Hvi c I evs nx Hn i). exact Hr.
  - apply srz_halt. exact Hh.
  - apply (srz_sloop segs (cwrom c r) (loop_wrom P) (silent_loop_wrom P Hl)).
    exists c, r. split; [exact HP|]. split; [exact Hr | reflexivity].
  - eapply srz_conseq; [apply IH; exact Hr | exact Heq].
Qed.
End Seg.

(** * The run's segment list *)
Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Lemma silent_loop_app_tail : forall P, silent_loop segs P -> silent_loop (segs ++ tail) P.
  Proof.
    intros P Hl c HP. destruct (Hl c HP) as (Hh & Hsvc & ms' & m' & Hacc & HP').
    split; [exact Hh|]. split; [exact Hsvc|].
    exists ms', m'. split; [| exact HP'].
    exact (mi_account_step_app_nx segs tail Hnx Hnw _ _ _ Hacc).
  Qed.

  Theorem srealizes_app_tail : forall c T, srealizes segs c T -> srealizes (segs ++ tail) c T.
  Proof.
    intros c T H;
      induction H as [c I evs nx T i0 Hn Hrob Hc IH | c Hh | c P Hl HP | c T T' H IH Heq].
    - apply (srz_node (segs ++ tail) c I evs nx T i0); [| | exact IH].
      + change (rnode_ok (segs ++ tail) c I evs nx).
        exact (node_ok_app_tail segs tail Hnx Hnw Hvi c I evs nx i0 Hn).
      + exact (sys_rob_app_tail segs tail Hnw c Hrob).
    - exact (srz_halt (segs ++ tail) c Hh).
    - exact (srz_sloop (segs ++ tail) c P (silent_loop_app_tail P Hl) HP).
    - exact (srz_conseq (segs ++ tail) c T T' IH Heq).
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

(** * The run's own start *)
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
