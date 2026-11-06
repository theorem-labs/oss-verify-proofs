(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import RegEqv.
From OSSVerify.Proofs.openssl.ct.lib.AS Require ShapeAlg ShapeHalts.
From OSSVerify.Proofs.openssl.ct.lib.A Require SrzEqv.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require ShapeAlg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require ShapeAlgCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module D := OSSVerify.Proofs.openssl.ct.lib.AS.ShapeAlg.
Module K := OSSVerify.Proofs.openssl.ct.lib.VCommon.ShapeAlg.
Module KC := OSSVerify.Proofs.openssl.ct.lib.VCommon.ShapeAlgCfg.

Section Bridge.
Variable segs : list Segment.

Theorem realizes_cfg_of_realizes : forall c (T : D.TSet), D.realizes segs c T -> KC.realizes_cfg segs ncfg c T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (KC.rzc_node segs ncfg c I evs nx T i0 Hnode IH).
  - exact (KC.rzc_halt segs ncfg c Hh).
  - exact (KC.rzc_conseq segs ncfg c T T' IH Heq).
Qed.

Theorem realizes_cfg_of_realizes_eqv : forall c1 c2 (T : D.TSet),
  D.realizes segs c1 T -> cfg_eqv c1 c2 -> KC.realizes_cfg segs ncfg c2 T.
Proof. intros c1 c2 T H He. apply realizes_cfg_of_realizes. exact (SrzEqv.realizes_eqv segs c1 T H c2 He). Qed.

End Bridge.

(* [comment removed for export] *)
Theorem T_canon_cfg (tsegs : list Segment) (tpc : N) (tph : PhdrInfo) (lim : Z) (en : ExecEntry) (inp : ProcInput) (T : K.TSet) :
  KC.realizes_cfg tsegs ncfg
    (init_config tsegs tpc tph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) T ->
  trace_equiv (bh_traces (Run.run_scfg ncfg (mkImage tsegs tpc tph) lim en inp)) T
  /\ ~ bh_errors (Run.run_scfg ncfg (mkImage tsegs tpc tph) lim en inp).
Proof.
  intros Hr. destruct en as [sp brk mb rnd]. cbn [Run.run_scfg bh_traces bh_errors en_sp en_brk en_mmap_base en_draw] in *.
  split.
  - intros tr. exact (KC.realizes_cfg_obs_iff tsegs ncfg _ _ Hr tr).
  - exact (KC.realizes_cfg_no_error tsegs ncfg _ _ Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Halts.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Theorem realizes_cfg_must_exit : forall (S : list word) c (T : K.TSet),
  KC.realizes_cfg segs cfg c T ->
  forall pre, (forall tr, T tr -> (forall e, In e (pre ++ tr) -> ~ ShapeHalts.ev_is_kill e)
                               /\ (forall tr0 code fs, pre ++ tr = tr0 ++ [ExitEv code fs] -> In code S)) ->
  m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg cfg segs S c.
Proof.
  intros S c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c S0 HS Hinv Hfalse | c T T' H IH Heq]; intros pre HT Hnh.
  - destruct Hnode as [Hcomp Hsound].
    apply must_exit_in_at_cfg_running; [exact Hnh | | |].
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e Herr. destruct (Hsound e SError Herr) as (i & _ & Hbad). discriminate Hbad.
    + intros e c' Hss. destruct (Hsound e (SNext c') Hss) as (i & -> & Hc'). injection Hc' as ->.
      destruct (sstep_cfg_next_halts_by_exit segs cfg c (evs i) (nx i) Hss)
        as [Hn | [(evs0 & code & Hev & Hh & Hk) | (evs0 & sig & Hev & Hk)]].
      * apply (IH i (pre ++ evs i)); [| exact Hn].
        intros tr Htr.
        assert (HTi : K.t_alt (fun i => K.t_emit (evs i) (T i)) (evs i ++ tr)).
        { exists i. right. exists tr. split; [reflexivity | exact Htr]. }
        destruct (HT _ HTi) as [Hnk Hex]. rewrite <- app_assoc. split; [exact Hnk | exact Hex].
      * assert (HTi : K.t_alt (fun i => K.t_emit (evs i) (T i)) (evs i)).
        { exists i. left. apply is_prefix_refl. }
        destruct (HT _ HTi) as [_ Hex].
        apply (must_exit_in_at_cfg_halted cfg segs S (nx i) code Hh); [| exact Hk].
        apply (Hex (pre ++ evs0) code (m_fs (cfg_model (nx i)))). rewrite Hev, app_assoc. reflexivity.
      * exfalso.
        assert (HTi : K.t_alt (fun i => K.t_emit (evs i) (T i)) (evs i)).
        { exists i. left. apply is_prefix_refl. }
        destruct (HT _ HTi) as [Hnk _].
        apply (Hnk (KillEv sig (m_fs (cfg_model (nx i))))); [| exact Logic.I].
        apply in_or_app. right. rewrite Hev. apply in_or_app. right. left. reflexivity.
  - congruence.
  - destruct Hfalse.
  - apply (IH pre); [| exact Hnh]. intros tr Htr. apply HT. apply Heq. exact Htr.
Qed.

End Halts.

Corollary realizes_cfg_must_exit_forced_only : forall segs (S : list word) c (T : K.TSet),
  KC.realizes_cfg segs ncfg c T -> ShapeHalts.shape_exits_in S T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof.
  intros segs S c T Hr HT Hnh.
  apply (must_exit_in_at_cfg_mono forced_only_cfg ncfg segs S c).
  - apply forced_only_cfg_least.
  - apply ShapeHalts.decided_from_classic.
  - apply (realizes_cfg_must_exit segs ncfg S c T Hr []); [| exact Hnh]. intros tr Htr. cbn [app]. exact (HT tr Htr).
Qed.
