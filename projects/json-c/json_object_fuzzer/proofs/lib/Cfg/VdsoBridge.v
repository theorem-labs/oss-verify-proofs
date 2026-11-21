(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the vDSO layer of the run's start, for json-c's [QRjH.realizes].
   Restated from projects/boost-json/fuzz_parse/proofs/lib/Common/VdsoBridge.v (itself from
   coturn/FuzzStunClient's lib/Common/VdsoBridge.v), over this tree's [QRjH.realizes], whose nodes step by
   [sstep_cfg segs (alloc_only_cfg false)], with the two forms json-c's realizes has and the source's does
   not: the loop node [rz_loop] (its exit path a [star_rob] path) and its mutual [lbody].

   Under a caller invariant [P] that keeps every visited pc away from an exported vDSO entry and survives
   a step, a derivation from [c] is one from [c] under any vDSO draw ([cfg_with_vdso v c]).  The
   completeness half of a node comes from the model's forward frame lemma applied with the original's own
   draw ([cfg_with_vdso_back]); the wrapped node's children are [cfg_with_vdso w (nx i)] for the w the
   step leaves, so each node is re-indexed over the witnessed transitions and the recursion is
   generalised over the draw.  A loop's invariant [V] becomes [Vw V], its members under any draw. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Vdso Run VdsoCommute VdsoCommuteSys VdsoCommuteCfg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomBase.
Import ListNotations.

Section VdsoBridge.
Variable segs : list Segment.
Local Notation scfg := (alloc_only_cfg false).

Lemma cfg_with_vdso_back : forall v c, cfg_with_vdso (m_vdso (cfg_model c)) (cfg_with_vdso v c) = c.
Proof.
  intros v [ms m]. unfold cfg_with_vdso. cbn [cfg_ms cfg_model].
  rewrite with_vdso_idem, with_vdso_same. reflexivity.
Qed.

Lemma cfg_with_vdso_absorb : forall w v c, cfg_with_vdso w (cfg_with_vdso v c) = cfg_with_vdso w c.
Proof. intros w v [ms m]. unfold cfg_with_vdso. cbn [cfg_ms cfg_model]. rewrite with_vdso_idem. reflexivity. Qed.

Lemma cfg_with_vdso_self : forall c, cfg_with_vdso (m_vdso (cfg_model c)) c = c.
Proof. intros [ms m]. unfold cfg_with_vdso. cbn [cfg_ms cfg_model]. rewrite with_vdso_same. reflexivity. Qed.

Lemma m_halted_with_vdso : forall v m, m_halted (with_vdso v m) = m_halted m.
Proof. intros v [fd vm io fs pr lim tm]; destruct vm; reflexivity. Qed.

(* The transitions the wrapped state takes, indexed by the original node's index. *)
Definition wI (c : config) (I : Type) (evs : I -> list event) (nx : I -> config) (v : VdsoRun) : Type :=
  {i : I & {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                           /\ sstep_cfg segs scfg (cfg_with_vdso v c) (evs i) (SNext c'')}}.

(* A node at [c] is a node at [cfg_with_vdso v c], over the transitions the wrapped state takes. *)
Lemma node_ok_vdso : forall c (I : Type) (evs : I -> list event) (nx : I -> config) v,
  QRjH.node_ok segs c I evs nx -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None ->
  QRjH.node_ok segs (cfg_with_vdso v c) (wI c I evs nx v)
    (fun i' => evs (projT1 i')) (fun i' => proj1_sig (projT2 i')).
Proof.
  intros c I evs nx v [Hs Hc] Hnv. split.
  - intros [i [c'' Hp]]. exact (proj2 Hp).
  - intros e st Hst.
    pose proof (sstep_cfg_vdso_frame_c segs scfg (m_vdso (cfg_model c)) (cfg_with_vdso v c) e st Hnv Hst)
      as Hinv.
    rewrite cfg_with_vdso_back in Hinv.
    destruct (Hc e _ Hinv) as (i & -> & Hst').
    destruct st as [c''|]; cbn [step_to_with_vdso] in Hst'; [|discriminate].
    injection Hst' as Hc''.
    assert (Hw : c'' = cfg_with_vdso (m_vdso (cfg_model c'')) (nx i)).
    { rewrite <- Hc'', cfg_with_vdso_absorb, cfg_with_vdso_self. reflexivity. }
    exists (@existT I (fun i => {c0 : config | (exists w, c0 = cfg_with_vdso w (nx i))
                                  /\ sstep_cfg segs scfg (cfg_with_vdso v c) (evs i) (SNext c0)})
              i (exist _ c'' (conj (ex_intro _ _ Hw) Hst))). split; reflexivity.
Qed.

Variable P : config -> Prop.
Hypothesis Hpc : forall c, P c -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None.
Hypothesis Hstep : forall c evs c', P c -> sstep_cfg segs scfg c evs (SNext c') -> P c'.

(* the loop's exit path, under any draw *)
Lemma star_rob_vdso : forall c c_e, QRjH.star_rob segs c c_e -> P c ->
  P c_e /\ forall v, QRjH.star_rob segs (cfg_with_vdso v c) (cfg_with_vdso v c_e).
Proof.
  intros c c_e H. induction H as [c | c c1 c2 Hs Hrob Hd IH]; intros HP.
  - split; [exact HP | intros v; apply QRjH.srob_refl].
  - destruct (IH (Hstep c [] c1 HP Hs)) as [HP2 IH2]. split; [exact HP2|]. intros v.
    apply (QRjH.srob_step segs (cfg_with_vdso v c) (cfg_with_vdso v c1) (cfg_with_vdso v c2)).
    + exact (sstep_cfg_vdso_frame_c segs scfg v c [] (SNext c1) (Hpc c HP) Hs).
    + exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
    + exact (IH2 v).
Qed.

(* a loop invariant's members under any draw *)
Definition Vw (V : config -> Prop) (c' : config) : Prop :=
  exists c0 w, V c0 /\ P c0 /\ c' = cfg_with_vdso w c0.

Theorem realizes_with_vdso_mut :
  (forall c T, QRjH.realizes segs c T -> P c -> forall v, QRjH.realizes segs (cfg_with_vdso v c) T)
  /\ (forall V T c, QRjH.lbody segs V T c -> P c -> forall v, QRjH.lbody segs (Vw V) T (cfg_with_vdso v c)).
Proof.
  apply (QRjH.realizes_lbody_mutind segs
    (fun c T _ => P c -> forall v, QRjH.realizes segs (cfg_with_vdso v c) T)
    (fun V T c _ => P c -> forall v, QRjH.lbody segs (Vw V) T (cfg_with_vdso v c))).
  - intros c I evs nx T i0 Hnode Hrob Hcont IH HP v.
    pose proof (Hpc c HP) as Hnv.
    assert (W : forall i, sstep_cfg segs scfg (cfg_with_vdso v c) (evs i) (SNext (cfg_with_vdso v (nx i))))
      by (intros i; exact (sstep_cfg_vdso_frame_c segs scfg v c (evs i) (SNext (nx i)) Hnv (proj1 Hnode i))).
    set (pick := fun i : I => (
           @existT I (fun i => {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                               /\ sstep_cfg segs scfg (cfg_with_vdso v c) (evs i) (SNext c'')})
             i (exist _ (cfg_with_vdso v (nx i)) (conj (ex_intro _ v eq_refl) (W i))) : wI c I evs nx v)).
    apply (QRjH.rz_conseq segs _ (QRjH.t_alt (fun i' : wI c I evs nx v => QRjH.t_emit (evs (projT1 i')) (T (projT1 i'))))).
    + apply (QRjH.rz_node segs _ (wI c I evs nx v) (fun i' => evs (projT1 i')) (fun i' => proj1_sig (projT2 i'))
               (fun i' => T (projT1 i')) (pick i0)).
      * exact (node_ok_vdso c I evs nx v Hnode Hnv).
      * exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
      * intros [i [c'' Hp]]. cbn [projT1 projT2 proj1_sig]. destruct (proj1 Hp) as [w Hw]. rewrite Hw.
        exact (IH i (Hstep c (evs i) (nx i) HP (proj1 Hnode i)) w).
    + intros tr. split.
      * intros [[i s] Hi]. exists i. exact Hi.
      * intros [i Hi]. exists (pick i). exact Hi.
  - intros c Hh HP v. apply QRjH.rz_halt. unfold cfg_with_vdso. cbn [cfg_model].
    rewrite m_halted_with_vdso. exact Hh.
  - intros c T T' H IH Heq HP v. eapply QRjH.rz_conseq; [exact (IH HP v) | exact Heq].
  - intros V T c c_e HV Hbody IHbody Hw He IHe HP v.
    destruct (star_rob_vdso c c_e Hw HP) as [HPe Hwv].
    apply (QRjH.rz_loop segs (Vw V) T (cfg_with_vdso v c) (cfg_with_vdso v c_e)).
    + exists c, v. split; [exact HV|]. split; [exact HP | reflexivity].
    + intros c' (c0 & w & HV0 & HP0 & ->). exact (IHbody c0 HV0 HP0 w).
    + exact (Hwv v).
    + exact (IHe HPe v).
  - intros V T c H IH HP v. apply QRjH.lb_exit. exact (IH HP v).
  - intros V T c I nx k Hnode Hrob Hk IHk Hv HP v.
    pose proof (Hpc c HP) as Hnv.
    apply (QRjH.lb_node segs (Vw V) T (cfg_with_vdso v c) (wI c I (fun _ => []) nx v)
             (fun i' => proj1_sig (projT2 i')) (fun i' => k (projT1 i'))).
    + exact (node_ok_vdso c I (fun _ => []) nx v Hnode Hnv).
    + exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
    + intros [i [c'' Hp]] Hki. cbn [projT1 projT2 proj1_sig] in *. destruct (proj1 Hp) as [w ->].
      exact (IHk i Hki (Hstep c [] (nx i) HP (proj1 Hnode i)) w).
    + intros [i [c'' Hp]] Hki. cbn [projT1 projT2 proj1_sig] in *. destruct (proj1 Hp) as [w ->].
      exists (nx i), w. split; [exact (Hv i Hki)|]. split; [exact (Hstep c [] (nx i) HP (proj1 Hnode i)) | reflexivity].
Qed.

Theorem realizes_with_vdso : forall c T, QRjH.realizes segs c T -> P c ->
  forall v, QRjH.realizes segs (cfg_with_vdso v c) T.
Proof. exact (proj1 realizes_with_vdso_mut). Qed.
End VdsoBridge.

(** Over a segment list with no vDSO text every pc is away from an exported entry
    ([vdso_entry_fn_none_of_no_text]), so [P := True] serves. *)
Corollary realizes_with_vdso_no_text : forall segs,
  vdso_text_seg segs = None ->
  forall c T, QRjH.realizes segs c T -> forall v, QRjH.realizes segs (cfg_with_vdso v c) T.
Proof.
  intros segs Hnt c T H v.
  apply (realizes_with_vdso segs (fun _ => True)); [ | | exact H | exact I].
  - intros c' _. exact (vdso_entry_fn_none_of_no_text segs _ Hnt).
  - intros; exact I.
Qed.
