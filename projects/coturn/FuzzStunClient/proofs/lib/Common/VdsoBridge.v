(* Bridge (A) for coturn's top (RefMain): the with_vdso composition for [ShapeAlg.realizes].
   It uses the model's theories/LinuxProcessSem/VdsoCommuteSys.v and VdsoCommute.v.  The LPS walk is
   [syscall_spec_vdso_commutes] (no hypothesis) and, at the step layer, [sstep_cfg_with_vdso]
   per state on [vdso_entry_fn segs pc = None].  This lifts that to coturn's plan relation
   [ShapeAlg.realizes] under a caller invariant [P], exactly as [star_with_vdso] does for [star]:
   [P] keeps every visited pc away from an exported vDSO entry and survives a step.

   The completeness half of a node needs the INVERSE direction: a step from the wrapped
   configuration is a step from the original.  It comes from the same forward lemma applied with
   the original's own draw: [cfg_with_vdso (m_vdso m) (cfg_with_vdso v c) = c]
   ([with_vdso_idem], [with_vdso_same]).  The wrapped node's children are then
   [cfg_with_vdso w (nx i)] for the w the step leaves, so the node is re-indexed over the
   witnessed transitions and the recursion is generalised over the draw. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run VdsoCommute VdsoCommuteSys.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.

Section VdsoBridge.
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
  (forall c evs c', P c -> sstep segs c evs (SNext c') -> P c') ->
  forall c T, realizes segs c T -> P c -> forall v, realizes segs (cfg_with_vdso v c) T.
Proof.
  intros P Hpc Hstep c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq]; intros HP v.
  - destruct Hnode as [Hs Hc].
    pose proof (Hpc c HP) as Hnv.
    (* the forward image of each original transition *)
    assert (W : forall i, sstep segs (cfg_with_vdso v c) (evs i) (SNext (cfg_with_vdso v (nx i)))).
    { intros i. exact (sstep_cfg_with_vdso segs v c (evs i) (SNext (nx i)) Hnv (Hs i)). }
    set (I' := {i : I & {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                        /\ sstep segs (cfg_with_vdso v c) (evs i) (SNext c'')}}).
    set (pick := fun i : I => @existT I (fun i => {c'' : config | (exists w, c'' = cfg_with_vdso w (nx i))
                                        /\ sstep segs (cfg_with_vdso v c) (evs i) (SNext c'')})
                                     i (exist _ (cfg_with_vdso v (nx i)) (conj (ex_intro _ v eq_refl) (W i)))).
    apply (rz_conseq segs _ (t_alt (fun i' : I' => t_emit (evs (projT1 i')) (T (projT1 i'))))).
    + apply (rz_node segs _ I' (fun i' => evs (projT1 i')) (fun i' => proj1_sig (projT2 i'))
               (fun i' => T (projT1 i')) (pick i0)).
      * split.
        -- intros [i [c'' Hp]]. exact (proj2 Hp).
        -- intros e st Hst.
           assert (Hnv' : vdso_entry_fn segs (ms_pc (cfg_ms (cfg_with_vdso v c))) = None) by exact Hnv.
           pose proof (sstep_cfg_with_vdso segs (m_vdso (cfg_model c)) (cfg_with_vdso v c) e st Hnv' Hst) as Hinv.
           rewrite cfg_with_vdso_back in Hinv.
           destruct (Hc e _ Hinv) as (i & -> & Hst').
           destruct st as [c''|]; cbn [step_to_with_vdso] in Hst'; [|discriminate].
           injection Hst' as Hc''.
           assert (Hw : c'' = cfg_with_vdso (m_vdso (cfg_model c'')) (nx i)).
           { rewrite <- Hc'', cfg_with_vdso_absorb, cfg_with_vdso_self. reflexivity. }
           exists (@existT I _ i (exist _ c'' (conj (ex_intro _ _ Hw) Hst))). split; reflexivity.
      * (* (B2): [rz_node] asks [RomBase.sys_rob], and this node's
           configuration is the original's under a different vDSO draw.  [sys_rob] is quantified
           over that layer precisely so this is one lemma and not a transport
           (Common/Cfg/RomBase.v:154-192). *)
        exact (RomBase.sys_rob_cfg_with_vdso segs v c Hrob).
      * intros [i [c'' Hp]]. cbn [projT1 projT2 proj1_sig]. destruct (proj1 Hp) as [w Hw]. rewrite Hw.
        exact (IH i (Hstep c (evs i) (nx i) HP (Hs i)) w).
    + intros tr. split.
      * intros [[i s] Hi]. exists i. exact Hi.
      * intros [i Hi]. exists (pick i). exact Hi.
  - apply rz_halt. unfold cfg_with_vdso. cbn [cfg_model]. rewrite m_halted_with_vdso. exact Hh.
  - eapply rz_conseq; [exact (IH HP v) | exact Heq].
Qed.

(* THE TOP-LEVEL DISCHARGE, and why no pc invariant is needed at coturn's top.  coturn's plans are
   all proved over the IMAGE's segment list RSEGS (Plain.M.loaded_segments), which carries no vDSO
   text: [vdso_text_seg RSEGS = None] is a closed computation.  So apply (A) over RSEGS FIRST, where
   LPS's [vdso_entry_fn_none_of_no_text] discharges the premise at EVERY pc (P := True), and only
   then lift the wrapped derivation to [run_segments] with (B).  [vdso_entry_fn_none_of_no_text] is
   false over [run_segments], which is exactly why (A) must come before (B) and not after; (B) is
   generic in the model, so it carries the wrapped configuration unchanged. *)
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
