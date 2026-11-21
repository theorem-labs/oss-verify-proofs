(* SPDX-License-Identifier: MIT *)
(* Restated from coturn/FuzzStunClient's lib/Common/VdsoBridge.v for the LPS 727298f3 port of this
   tree's top statements: the same proof over this tree's [ShapeAlg.realizes], whose nodes step by
   [sstep_cfg segs the_scfg], with the model's [VdsoCommuteCfg.sstep_cfg_vdso_frame_c] in place of
   coturn's [sstep_cfg_with_vdso].

   (A), the with_vdso composition for [ShapeAlg.realizes]: under a caller invariant [P] that keeps
   every visited pc away from an exported vDSO entry and survives a step, a derivation from [c] is
   one from [c] under any vDSO draw.  The completeness half of a node needs the inverse direction;
   it comes from the same forward lemma applied with the original's own draw:
   [cfg_with_vdso (m_vdso m) (cfg_with_vdso v c) = c] ([with_vdso_idem], [with_vdso_same]).  The
   wrapped node's children are [cfg_with_vdso w (nx i)] for the w the step leaves, so the node is
   re-indexed over the witnessed transitions and the recursion is generalised over the draw. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run VdsoCommute VdsoCommuteSys VdsoCommuteCfg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg ShapeAlg.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase.

Section VdsoBridge.
Context {SC : StepCfg}.
Variable segs : list Segment.

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

Theorem realizes_with_vdso : forall (P : config -> Prop),
  (forall c, P c -> vdso_entry_fn segs (ms_pc (cfg_ms c)) = None) ->
  (forall c evs c', P c -> sstep_cfg segs the_scfg c evs (SNext c') -> P c') ->
  forall c T, realizes segs c T -> P c -> forall v, realizes segs (cfg_with_vdso v c) T.
Proof.
  intros P Hpc Hstep c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq]; intros HP v.
  - destruct Hnode as [Hs Hc].
    pose proof (Hpc c HP) as Hnv.
    assert (W : forall i, sstep_cfg segs the_scfg (cfg_with_vdso v c) (evs i) (SNext (cfg_with_vdso v (nx i)))).
    { intros i. exact (sstep_cfg_vdso_frame_c segs the_scfg v c (evs i) (SNext (nx i)) Hnv (Hs i)). }
    set (I' := {i : I & {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                        /\ sstep_cfg segs the_scfg (cfg_with_vdso v c) (evs i) (SNext c'')}}).
    set (pick := fun i : I => @existT I (fun i => {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                        /\ sstep_cfg segs the_scfg (cfg_with_vdso v c) (evs i) (SNext c'')})
                                     i (exist _ (cfg_with_vdso v (nx i)) (conj (ex_intro _ v eq_refl) (W i)))).
    apply (rz_conseq segs _ (t_alt (fun i' : I' => t_emit (evs (projT1 i')) (T (projT1 i'))))).
    + apply (rz_node segs _ I' (fun i' => evs (projT1 i')) (fun i' => proj1_sig (projT2 i'))
               (fun i' => T (projT1 i')) (pick i0)).
      * split.
        -- intros [i [c'' Hp]]. exact (proj2 Hp).
        -- intros e st Hst.
           assert (Hnv' : vdso_entry_fn segs (ms_pc (cfg_ms (cfg_with_vdso v c))) = None) by exact Hnv.
           pose proof (sstep_cfg_vdso_frame_c segs the_scfg (m_vdso (cfg_model c)) (cfg_with_vdso v c) e st Hnv' Hst)
             as Hinv.
           rewrite cfg_with_vdso_back in Hinv.
           destruct (Hc e _ Hinv) as (i & -> & Hst').
           destruct st as [c''|]; cbn [step_to_with_vdso] in Hst'; [|discriminate].
           injection Hst' as Hc''.
           assert (Hw : c'' = cfg_with_vdso (m_vdso (cfg_model c'')) (nx i)).
           { rewrite <- Hc'', cfg_with_vdso_absorb, cfg_with_vdso_self. reflexivity. }
           exists (@existT I _ i (exist _ c'' (conj (ex_intro _ _ Hw) Hst))). split; reflexivity.
      * (* [RomBase.sys_rob] is quantified over the vDSO layer, so it moves in one lemma *)
        exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
      * intros [i [c'' Hp]]. cbn [projT1 projT2 proj1_sig]. destruct (proj1 Hp) as [w Hw]. rewrite Hw.
        exact (IH i (Hstep c (evs i) (nx i) HP (Hs i)) w).
    + intros tr. split.
      * intros [[i s] Hi]. exists i. exact Hi.
      * intros [i Hi]. exists (pick i). exact Hi.
  - apply rz_halt. unfold cfg_with_vdso. cbn [cfg_model]. rewrite m_halted_with_vdso. exact Hh.
  - eapply rz_conseq; [exact (IH HP v) | exact Heq].
Qed.

(** Over a segment list with no vDSO text every pc is away from an exported entry
    ([vdso_entry_fn_none_of_no_text]), so [P := True] serves. *)
Corollary realizes_with_vdso_no_text :
  vdso_text_seg segs = None ->
  forall c T, realizes segs c T -> forall v, realizes segs (cfg_with_vdso v c) T.
Proof.
  intros Hnt c T H v.
  apply (realizes_with_vdso (fun _ => True)); [ | | exact H | exact I].
  - intros c' _. exact (vdso_entry_fn_none_of_no_text segs _ Hnt).
  - intros; exact I.
Qed.

End VdsoBridge.
