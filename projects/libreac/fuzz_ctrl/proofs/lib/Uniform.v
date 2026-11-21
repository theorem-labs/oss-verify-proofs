From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require RoomShapesDraft AgreeLim.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require RomBase RomStableK YK15.
Import ListNotations.

Ltac sys_outcome_cases H :=
  unfold err_ret, ret_only, errno_from, bind, pure, choose, alt, get_model, modify, unmodeled in H;
  cbv beta iota zeta in H;
  repeat match goal with
  | H0 : _ /\ _ |- _ => destruct H0
  | H0 : exists _, _ |- _ => destruct H0
  | H0 : _ \/ _ |- _ => destruct H0
  | H0 : Ok _ _ _ = Ok _ _ _ |- _ => injection H0; clear H0; intros; subst
  | H0 : Ok _ _ _ = Unmodeled |- _ => discriminate H0
  | H0 : Unmodeled = Ok _ _ _ |- _ => discriminate H0
  | H0 : context [if ?b then _ else _] |- _ => destruct b; cbv beta iota in H0
  end.

Ltac proc_kept FR :=
  unfold with_mmap_replacement, with_mmap_destroyed, with_mmap_backing, with_brk_next, mremap_model_next;
  cbv beta zeta;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  rewrite ?FR; reflexivity.

Section Uniform.
Variable segs : list Segment.

Lemma placement_events_eq : forall c x8 len e1 c1 e2 c2,
  RoomShapesDraft.placement_at segs c x8 len ->
  sstep_cfg segs ACFG c e1 (SNext c1) -> sstep_cfg segs ACFG c e2 (SNext c2) -> e1 = e2.
Proof.
  assert (FR : forall l m0, m_proc (forget_vm_ranges l m0) = m_proc m0).
  { induction l as [|[a n] l IH]; intros m0; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. }
  assert (Q : forall i m len eff m' evs, RoomShapesDraft.placement_len i m = Some len ->
      syscall_spec i m (Ok eff m' evs) -> evs = [] /\ m_proc m' = m_proc m).
  { intros i m len eff m' evs Hl Hs.
    unfold RoomShapesDraft.placement_len in Hl. cbv zeta in Hl. revert Hl Hs.
    destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 222) as [E|_].
    - intros _ Hs.
      assert (Hm : mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)
          i m (Ok eff m' evs)).
      { revert Hs. unfold syscall_spec, dispatch. cbv beta. rewrite E. intro H. exact H. }
      (* mmap_fixed_overflow must be unfolded here or sys_outcome_cases enumerates
         nothing on that branch and evs stays free, giving "Unable to unify [] with
         evs".  Measured at the shas rather than inferred: mmap_spec's BODY mentions
         mmap_fixed_overflow 5 times at 75d69e00 and 0 times at f1006fe8, while
         err_ret in that body drops 26 -> 21 - the revision SUBSTITUTED the new
         definition for four err_ret ENOMEM arms.  (A bare grep for the name at
         f1006fe8 returns two hits; both are the Example names
         mmap_fixed_overflowing_len_*, a prefix collision, not the definition.)
         Diagnosis and cure from RepairG1Injected, which found the same line in
         nine trees; the cause above is re-measured here. *)
      clear Hs. unfold mmap_spec, mmap_fixed_overflow in Hm. sys_outcome_cases Hm; (split; [reflexivity | proc_kept FR]).
    - destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 216) as [E|_].
      + intros _ Hs.
        assert (Hm : mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m (Ok eff m' evs)).
        { revert Hs. unfold syscall_spec, dispatch. cbv beta. rewrite E. intro H. exact H. }
        clear Hs. unfold mremap_spec in Hm. sys_outcome_cases Hm; (split; [reflexivity | proc_kept FR]).
      + destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 214) as [E|_]; [| intros Hl; discriminate Hl].
        intros _ Hs.
        assert (Hm : brk_spec (in_arg i 0) i m (Ok eff m' evs)).
        { revert Hs. unfold syscall_spec, dispatch. cbv beta. rewrite E. intro H. exact H. }
        clear Hs. unfold brk_spec in Hm. sys_outcome_cases Hm; (split; [reflexivity | proc_kept FR]). }
  assert (S : forall ms md x8 len e c', m_halted md = None -> ms_svc_pending ms = Some x8 ->
      RoomShapesDraft.placement_len (sys_input segs ms x8) md = Some len ->
      sstep_cfg segs ACFG (mkCfg ms md) e (SNext c') -> e = []).
  { intros ms md x8 len e c' Hh Hsvc Hl Hs.
    inversion Hs; subst; rewrite Hsvc in *;
      repeat match goal with
      | Hp : Some _ = Some _ |- _ => injection Hp; clear Hp; intros; subst
      | Hp : Some _ = None |- _ => discriminate Hp
      end.
    - match goal with HS : syscall_spec _ _ (Ok _ _ _) |- _ => exact (proj1 (Q _ _ _ _ _ _ Hl HS)) end.
    - exfalso.
      match goal with HS : syscall_spec _ _ (Ok _ ?md' _), HH : m_halted ?md' = Some _ |- _ =>
        destruct (Q _ _ _ _ _ _ Hl HS) as [_ EP]; unfold m_halted in HH, Hh; rewrite EP in HH; congruence end.
    - exfalso.
      match goal with HS : syscall_spec _ _ (Ok _ ?md' _), HK : m_killed ?md' = Some _ |- _ =>
        destruct (Q _ _ _ _ _ _ Hl HS) as [_ EP]; pose proof (m_killed_of_m_halted_none _ Hh) as K;
        unfold m_killed in HK, K; rewrite EP in HK; congruence end. }
  intros [ms md] x8 len e1 c1 e2 c2 (Hh & Hsvc & Hl) H1 H2.
  cbn [cfg_ms cfg_model] in Hh, Hsvc, Hl.
  rewrite (S ms md x8 len e1 c1 Hh Hsvc Hl H1), (S ms md x8 len e2 c2 Hh Hsvc Hl H2). reflexivity.
Qed.

Definition place_uniform (c : config) : Prop :=
  forall x8 len, RoomShapesDraft.placement_at segs c x8 len ->
  forall e1 c1 e2 c2, sstep_cfg segs ACFG c e1 (SNext c1) -> sstep_cfg segs ACFG c e2 (SNext c2) ->
    e1 = e2 /\ (forall tr, obs_trace_cfg segs ACFG c1 tr <-> obs_trace_cfg segs ACFG c2 tr).

(* POLICY-PINNED-TO-MODEL (Main, 2026-11-07).  [RoomShapesDraft.policy_pinned]
   is a CONJUNCT of the predicate every producer of [canon_fit_at] already
   builds, not a free-standing hypothesis: #38's [linux_place_is] pins the
   address and [linux_place_unique] makes it the only one, so the old form --
   quantified over every [policy_ok] policy with nothing tying it to the
   model -- was FALSE, not merely unproved.  The producers only ever
   ESTABLISH [canon_fit_at], so the obligation moves inward to them and no
   published file gains a premise. *)
Definition canon_fit_at (c : config) : Prop :=
  forall p s st, RoomShapesDraft.policy_ok p ->
  RoomShapesDraft.policy_pinned p s (cfg_model c) ->
  (page_round_down_Z (alloc_top (m_vmmaps (cfg_model c))) <= st)%Z ->
  (vm_limit (m_vmmaps (cfg_model c)) <= AgreeLim.LIM_AG)%Z ->
  forall x8 len, RoomShapesDraft.placement_at segs c x8 len ->
  (exists evs c', sstep_cfg segs ACFG c evs (SNext c')) ->
  RoomShapesDraft.canon_can_step p s st segs ACFG c.

Definition uniform (c : config) : Prop :=
  forall tr c', star_cfg segs ACFG c tr c' -> place_uniform c' /\ canon_fit_at c'.

Lemma uniform_here : forall c, uniform c -> place_uniform c.
Proof. intros c H. exact (proj1 (H [] c (star_cfg_refl segs ACFG c))). Qed.

Lemma uniform_fit_here : forall c, uniform c -> canon_fit_at c.
Proof. intros c H. exact (proj2 (H [] c (star_cfg_refl segs ACFG c))). Qed.

Lemma uniform_place : forall c tr c', uniform c -> star_cfg segs ACFG c tr c' -> place_uniform c'.
Proof. intros c tr c' H Hs. exact (proj1 (H tr c' Hs)). Qed.

Lemma uniform_fit : forall c tr c', uniform c -> star_cfg segs ACFG c tr c' -> canon_fit_at c'.
Proof. intros c tr c' H Hs. exact (proj2 (H tr c' Hs)). Qed.

Lemma uniform_step : forall c e c', uniform c -> sstep_cfg segs ACFG c e (SNext c') -> uniform c'.
Proof.
  intros c e c' H Hs tr c'' Hstar. apply (H (e ++ tr) c''). eapply star_cfg_step; [exact Hs | exact Hstar].
Qed.

Lemma uniform_intro : forall c, place_uniform c -> canon_fit_at c ->
  (forall e c', sstep_cfg segs ACFG c e (SNext c') -> uniform c') -> uniform c.
Proof.
  intros c Hp Hf Hs tr c' Hstar.
  inversion Hstar as [c0 | c1 evs c2 tr' c3 Hst Hstar']; subst; [exact (conj Hp Hf) | exact (Hs evs c2 Hst tr' c' Hstar')].
Qed.

Lemma uniform_placement : forall c, place_uniform c -> canon_fit_at c ->
  (forall e c', sstep_cfg segs ACFG c e (SNext c') -> uniform c') -> uniform c.
Proof. exact uniform_intro. Qed.

Lemma place_uniform_nonplacement : forall c,
  (forall x8 len, ~ RoomShapesDraft.placement_at segs c x8 len) -> place_uniform c.
Proof. intros c Hn x8 len Hp. exfalso. exact (Hn x8 len Hp). Qed.

Lemma canon_fit_at_nonplacement : forall c,
  (forall x8 len, ~ RoomShapesDraft.placement_at segs c x8 len) -> canon_fit_at c.
Proof. intros c Hn p s st _ _ _ _ x8 len Hp. exfalso. exact (Hn x8 len Hp). Qed.

Lemma uniform_nonplacement : forall c,
  (forall x8 len, ~ RoomShapesDraft.placement_at segs c x8 len) ->
  (forall e c', sstep_cfg segs ACFG c e (SNext c') -> uniform c') -> uniform c.
Proof.
  intros c Hn Hs. exact (uniform_intro c (place_uniform_nonplacement c Hn) (canon_fit_at_nonplacement c Hn) Hs).
Qed.

Lemma instr_not_placement : forall ms md x8 len,
  ms_svc_pending ms = None -> ~ RoomShapesDraft.placement_at segs (mkCfg ms md) x8 len.
Proof. intros ms md x8 len Hn (_ & Hs & _). cbn [cfg_ms] in Hs. congruence. Qed.

Lemma halted_not_placement : forall c x8 len,
  m_halted (cfg_model c) <> None -> ~ RoomShapesDraft.placement_at segs c x8 len.
Proof. intros c x8 len Hh (Hn & _). exact (Hh Hn). Qed.

Lemma nonalloc_not_placement : forall ms md x8 y8 len,
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  ~ RoomShapesDraft.placement_at segs (mkCfg ms md) y8 len.
Proof.
  intros ms md x8 y8 len Hsvc Hno (_ & Hs & Hl). cbn [cfg_ms cfg_model] in Hs, Hl.
  rewrite Hsvc in Hs. injection Hs as <-.
  unfold RoomShapesDraft.placement_len in Hl. cbv zeta in Hl.
  change (in_sysno (sys_input segs ms x8)) with x8 in Hl. revert Hl.
  destruct (Z.eqb_spec (bv_unsigned x8) 222) as [E|_]; [rewrite E in Hno; vm_compute in Hno; discriminate Hno|].
  destruct (Z.eqb_spec (bv_unsigned x8) 216) as [E|_]; [rewrite E in Hno; vm_compute in Hno; discriminate Hno|].
  destruct (Z.eqb_spec (bv_unsigned x8) 214) as [E|_]; [rewrite E in Hno; vm_compute in Hno; discriminate Hno|].
  intros Hl. discriminate Hl.
Qed.

Lemma uniform_halted : forall c, m_halted (cfg_model c) <> None -> uniform c.
Proof.
  intros c Hh tr c' Hstar. destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [_ ->].
  split; [apply place_uniform_nonplacement | apply canon_fit_at_nonplacement];
    intros x8 len; exact (halted_not_placement c x8 len Hh).
Qed.

End Uniform.

(* ------------------------------------------------------------------ *)
(* LPS 08b1429: the run reads [run_segments segs inp sp mb] from
   [init_config (run_segments ..) ..], so [AgreeCanon]'s canon half needs [uniform] there, while
   the walks stay over the binary's own segments.  [uniform] quantifies over every reachable
   configuration, so it is not a node-by-node lift: the walk bounds the reachable set, exactly as
   [RomStableK.cut_free_wrom] does, and at each node the two trace sets agree because both are the
   walk's own [T] ([YK15.realizes_obs_iff] on each side). *)
Section UniformRun.
Import RomBase RomStableK.

Lemma placement_at_wrom : forall segs c r x8 len,
  RoomShapesDraft.placement_at segs (cwrom c r) x8 len <-> RoomShapesDraft.placement_at segs c x8 len.
Proof.
  intros segs [ms m] r x8 len. unfold RoomShapesDraft.placement_at.
  cbn [cfg_ms cfg_model cwrom wrom ms_svc_pending].
  rewrite sys_input_wrom. unfold RoomShapesDraft.placement_len, with_mem, in_arg, in_sysno.
  cbn [in_args]. reflexivity.
Qed.

(** [placement_at] reads the input's number and arguments and the model, never its memory, and
    those come from the machine alone: the segment list does not enter. *)
Lemma placement_at_app : forall segs tail c x8 len,
  RoomShapesDraft.placement_at (segs ++ tail) c x8 len <-> RoomShapesDraft.placement_at segs c x8 len.
Proof.
  intros segs tail [ms m] x8 len. unfold RoomShapesDraft.placement_at.
  cbn [cfg_ms cfg_model]. unfold RoomShapesDraft.placement_len, in_sysno, in_arg, sys_input.
  cbn [in_args]. reflexivity.
Qed.

(** [canonical_ret] reads the input's number and arguments, the model and the specification of
    the answer, never [in_mem]'s bytes. *)
Lemma canonical_ret_wm_fwd : forall p s st i mp m ret,
  (forall o, syscall_spec (with_mem i mp) m o <-> syscall_spec i m o) ->
  RoomShapesDraft.canonical_ret p s st i m ret -> RoomShapesDraft.canonical_ret p s st (with_mem i mp) m ret.
Proof.
  intros p s st i mp m ret Hs H.
  assert (Hm : RoomShapesDraft.mremap_in_place p s (with_mem i mp) m <-> RoomShapesDraft.mremap_in_place p s i m).
  { unfold RoomShapesDraft.mremap_in_place. split.
    - intros [(eff & m' & evs & H1 & H2) H3].
      split; [exists eff, m', evs; split; [exact (proj1 (Hs _) H1) | exact H2] | exact H3].
    - intros [(eff & m' & evs & H1 & H2) H3].
      split; [exists eff, m', evs; split; [exact (proj2 (Hs _) H1) | exact H2] | exact H3]. }
  unfold RoomShapesDraft.canonical_ret in *.
  destruct H as [H | [H | [(E & [(Er & Hip) | (Hnip & Hf)]) | H]]].
  - left. exact H.
  - right. left. exact H.
  - right. right. left. split; [exact E|]. left. split; [exact Er | exact (proj2 Hm Hip)].
  - right. right. left. split; [exact E|]. right.
    split; [intros Hip; exact (Hnip (proj1 Hm Hip)) | exact Hf].
  - right. right. right. exact H.
Qed.

(** A canonical step of a node over its own segments is one over the run's segment list and
    backing: its system call reads the same specification over the larger backing ([sys_rob],
    node_ok's third conjunct), and [apply_effect_wrom] carries the backing through the answer. *)
Lemma canonical_step_lift : forall segs tail,
  (forall s, In s tail -> seg_writable s = false) ->
  forall p s st c c2 r, sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  RoomShapesDraft.canonical_step p s st segs c c2 ->
  RoomShapesDraft.canonical_step p s st (segs ++ tail) (cwrom c r) (cwrom c2 r).
Proof.
  intros segs tail Hnw p s st [ms m] c2 r Hrob Hr Hc x8 len Hpl.
  apply (proj1 (placement_at_app segs tail (cwrom (mkCfg ms m) r) x8 len)) in Hpl.
  apply (proj1 (placement_at_wrom segs (mkCfg ms m) r x8 len)) in Hpl.
  pose proof Hpl as [_ [Hsvc _]]. cbn [cfg_ms cfg_model] in Hsvc, Hr.
  destruct (Hc x8 len Hpl) as (eff & m' & evs & m'' & Hs & -> & Hret).
  cbn [cfg_ms cfg_model] in Hs, Hret.
  pose proof (fun o => Hrob r x8 Hr Hsvc o) as HS. cbn [cfg_ms cfg_model] in HS.
  exists eff, m', evs, m''. unfold cwrom. cbn [cfg_ms cfg_model].
  rewrite (sys_input_app_nw segs tail) by exact Hnw.
  split; [exact (proj2 (HS _) Hs)|].
  split; [first [reflexivity | rewrite apply_effect_wrom; reflexivity]|].
  exact (canonical_ret_wm_fwd p s st (sys_input segs ms x8) (ms_read_byte (wrom ms r)) m (eff_ret eff) HS Hret).
Qed.

(** The walk's nodes bound what the run can reach, so [uniform] carries to the run's segment list
    and backing together.  [T] is the walk's trace set on both sides. *)
Theorem uniform_lift : forall segs tail,
  (forall s, In s tail -> seg_executable s = false) ->
  (forall s, In s tail -> seg_writable s = false) ->
  vdso_image segs = None ->
  forall c T, @YK15.realizes segs AcfgMode c T -> YK15.cut_free segs c -> uniform segs c ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> uniform (segs ++ tail) (cwrom c r).
Proof.
  intros segs tail Hnx Hnw Hvi c T H.
  induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c T T' H IH Heq
                  | c I nx T i0 Hn Hc IH | c T Hb Hrb];
    intros NR HU r Hr.
  - apply uniform_intro.
    + intros x8 len Hpl e1 c1 e2 c2 H1 H2.
      pose proof (@node_ok_app_tail segs tail AcfgMode Hnx Hnw Hvi
                    (cwrom c r) I evs (fun i => cwrom (nx i) r) i0
                    (@node_wrom segs AcfgMode Hvi c I evs nx r Hn Hr)) as HN.
      destruct (proj1 (proj2 HN) e1 (SNext c1) H1) as (i & -> & Ei).
      destruct (proj1 (proj2 HN) e2 (SNext c2) H2) as (j & -> & Ej).
      injection Ei as ->. injection Ej as ->.
      assert (Hpl0 : RoomShapesDraft.placement_at segs c x8 len).
      { apply (proj1 (placement_at_wrom segs c r x8 len)).
        exact (proj1 (placement_at_app segs tail (cwrom c r) x8 len) Hpl). }
      destruct (uniform_here segs c HU x8 len Hpl0 (evs i) (nx i) (evs j) (nx j)
                  (proj1 Hn i) (proj1 Hn j)) as (Ee & Hobs).
      split; [exact Ee|].
      intros tr.
      assert (Ri : forall k, @YK15.realizes (segs ++ tail) AcfgMode (cwrom (nx k) r) (T k)).
      { intros k. apply (@realizes_app_tail segs tail AcfgMode Hnx Hnw Hvi).
        apply (@realizes_wrom segs AcfgMode Hvi _ (T k) (Hc k)).
        rewrite (@node_rom segs AcfgMode Hvi c I evs nx Hn k). exact Hr. }
      assert (Ci : forall k, YK15.cut_free (segs ++ tail) (cwrom (nx k) r)).
      { intros k.
        pose proof (YK15.cut_free_step segs c (evs k) (nx k) NR (proj1 Hn k)) as NRk.
        apply (@cut_free_app_tail segs tail Hnx Hnw Hvi _ (T k));
          [ apply (@realizes_wrom segs AcfgMode Hvi _ (T k) (Hc k));
            rewrite (@node_rom segs AcfgMode Hvi c I evs nx Hn k); exact Hr
          | apply (@cut_free_wrom segs Hvi _ (T k) (Hc k) NRk);
            rewrite (@node_rom segs AcfgMode Hvi c I evs nx Hn k); exact Hr ]. }
      rewrite (YK15.realizes_obs_iff (segs ++ tail) _ (T i) (Ri i) (Ci i) tr).
      rewrite (YK15.realizes_obs_iff (segs ++ tail) _ (T j) (Ri j) (Ci j) tr).
      rewrite <- (YK15.realizes_obs_iff segs (nx i) (T i) (Hc i)
                   (YK15.cut_free_step segs c (evs i) (nx i) NR (proj1 Hn i)) tr).
      rewrite <- (YK15.realizes_obs_iff segs (nx j) (T j) (Hc j)
                   (YK15.cut_free_step segs c (evs j) (nx j) NR (proj1 Hn j)) tr).
      exact (Hobs tr).
    + (* [canon_fit_at]: the node's canonical step over its own segments ([uniform_fit_here]) is
         one of the run's ([canonical_step_lift]); its step is the node's own over the run. *)
      intros p s st Hp Hpin Hst Hlim x8 len Hpl _.
      assert (Hpl0 : RoomShapesDraft.placement_at segs c x8 len).
      { apply (proj1 (placement_at_wrom segs c r x8 len)).
        exact (proj1 (placement_at_app segs tail (cwrom c r) x8 len) Hpl). }
      destruct (uniform_fit_here segs c HU p s st Hp Hpin Hst Hlim x8 len Hpl0
                  (ex_intro _ (evs i0) (ex_intro _ (nx i0) (proj1 Hn i0)))) as (e & c2 & Hs & Hcs).
      destruct (proj1 (proj2 Hn) e (SNext c2) Hs) as (i & -> & Ei). injection Ei as ->.
      pose proof (@node_ok_app_tail segs tail AcfgMode Hnx Hnw Hvi
                    (cwrom c r) I evs (fun i => cwrom (nx i) r) i0
                    (@node_wrom segs AcfgMode Hvi c I evs nx r Hn Hr)) as HN.
      exists (evs i), (cwrom (nx i) r). split; [exact (proj1 HN i)|].
      exact (canonical_step_lift segs tail Hnw p s st c (nx i) r (proj2 (proj2 Hn)) Hr Hcs).
    + intros e c' Hs.
      pose proof (@node_ok_app_tail segs tail AcfgMode Hnx Hnw Hvi
                    (cwrom c r) I evs (fun i => cwrom (nx i) r) i0
                    (@node_wrom segs AcfgMode Hvi c I evs nx r Hn Hr)) as HN.
      destruct (proj1 (proj2 HN) e (SNext c') Hs) as (i & -> & Ei). injection Ei as ->.
      apply (IH i (YK15.cut_free_step segs c (evs i) (nx i) NR (proj1 Hn i))
                 (uniform_step segs c (evs i) (nx i) HU (proj1 Hn i))).
      rewrite (@node_rom segs AcfgMode Hvi c I evs nx Hn i). exact Hr.
  (* [cwrom c r] is [mkCfg (wrom (cfg_ms c) r) (cfg_model c)] (Reusable/RomBase.v:25), so
     [cfg_model (cwrom c r)] is [cfg_model c] by conversion and Hh is already the premise.
     RomStableK.v:311 closes the same rz_halt obligation the same way. *)
  - apply uniform_halted. exact Hh.
  - exact (IH NR HU r Hr).
  - apply uniform_intro.
    + intros x8 len Hpl e1 c1 e2 c2 H1 H2.
      pose proof (@node_ok_app_tail segs tail AcfgMode Hnx Hnw Hvi
                    (cwrom c r) I (fun _ => []) (fun i => cwrom (nx i) r) i0
                    (@node_wrom segs AcfgMode Hvi c I (fun _ => []) nx r Hn Hr)) as HN.
      destruct (proj1 (proj2 HN) e1 (SNext c1) H1) as (i & -> & Ei).
      destruct (proj1 (proj2 HN) e2 (SNext c2) H2) as (j & -> & Ej).
      injection Ei as ->. injection Ej as ->.
      assert (Hpl0 : RoomShapesDraft.placement_at segs c x8 len).
      { apply (proj1 (placement_at_wrom segs c r x8 len)).
        exact (proj1 (placement_at_app segs tail (cwrom c r) x8 len) Hpl). }
      destruct (uniform_here segs c HU x8 len Hpl0 [] (nx i) [] (nx j)
                  (proj1 Hn i) (proj1 Hn j)) as (_ & Hobs).
      split; [reflexivity|].
      intros tr.
      assert (Ri : forall k, @YK15.realizes (segs ++ tail) AcfgMode (cwrom (nx k) r) (T k)).
      { intros k. apply (@realizes_app_tail segs tail AcfgMode Hnx Hnw Hvi).
        apply (@realizes_wrom segs AcfgMode Hvi _ (T k) (Hc k)).
        rewrite (@node_rom segs AcfgMode Hvi c I (fun _ => []) nx Hn k). exact Hr. }
      assert (Ci : forall k, YK15.cut_free (segs ++ tail) (cwrom (nx k) r)).
      { intros k.
        pose proof (YK15.cut_free_step segs c [] (nx k) NR (proj1 Hn k)) as NRk.
        apply (@cut_free_app_tail segs tail Hnx Hnw Hvi _ (T k));
          [ apply (@realizes_wrom segs AcfgMode Hvi _ (T k) (Hc k));
            rewrite (@node_rom segs AcfgMode Hvi c I (fun _ => []) nx Hn k); exact Hr
          | apply (@cut_free_wrom segs Hvi _ (T k) (Hc k) NRk);
            rewrite (@node_rom segs AcfgMode Hvi c I (fun _ => []) nx Hn k); exact Hr ]. }
      rewrite (YK15.realizes_obs_iff (segs ++ tail) _ (T i) (Ri i) (Ci i) tr).
      rewrite (YK15.realizes_obs_iff (segs ++ tail) _ (T j) (Ri j) (Ci j) tr).
      rewrite <- (YK15.realizes_obs_iff segs (nx i) (T i) (Hc i)
                   (YK15.cut_free_step segs c [] (nx i) NR (proj1 Hn i)) tr).
      rewrite <- (YK15.realizes_obs_iff segs (nx j) (T j) (Hc j)
                   (YK15.cut_free_step segs c [] (nx j) NR (proj1 Hn j)) tr).
      exact (Hobs tr).
    + intros p s st Hp Hpin Hst Hlim x8 len Hpl _.
      assert (Hpl0 : RoomShapesDraft.placement_at segs c x8 len).
      { apply (proj1 (placement_at_wrom segs c r x8 len)).
        exact (proj1 (placement_at_app segs tail (cwrom c r) x8 len) Hpl). }
      destruct (uniform_fit_here segs c HU p s st Hp Hpin Hst Hlim x8 len Hpl0
                  (ex_intro _ [] (ex_intro _ (nx i0) (proj1 Hn i0)))) as (e & c2 & Hs & Hcs).
      destruct (proj1 (proj2 Hn) e (SNext c2) Hs) as (i & -> & Ei). injection Ei as ->.
      pose proof (@node_ok_app_tail segs tail AcfgMode Hnx Hnw Hvi
                    (cwrom c r) I (fun _ => []) (fun i => cwrom (nx i) r) i0
                    (@node_wrom segs AcfgMode Hvi c I (fun _ => []) nx r Hn Hr)) as HN.
      exists [], (cwrom (nx i) r). split; [exact (proj1 HN i)|].
      exact (canonical_step_lift segs tail Hnw p s st c (nx i) r (proj2 (proj2 Hn)) Hr Hcs).
    + intros e c' Hs.
      pose proof (@node_ok_app_tail segs tail AcfgMode Hnx Hnw Hvi
                    (cwrom c r) I (fun _ => []) (fun i => cwrom (nx i) r) i0
                    (@node_wrom segs AcfgMode Hvi c I (fun _ => []) nx r Hn Hr)) as HN.
      destruct (proj1 (proj2 HN) e (SNext c') Hs) as (i & -> & Ei). injection Ei as ->.
      apply (IH i (YK15.cut_free_step segs c [] (nx i) NR (proj1 Hn i))
                 (uniform_step segs c [] (nx i) HU (proj1 Hn i))).
      rewrite (@node_rom segs AcfgMode Hvi c I (fun _ => []) nx Hn i). exact Hr.
  - exfalso. exact (YK15.cut_free_here segs c NR Hb).
Qed.

(** The run's own start.  [AgreeCanon.canon_spec_of_rz] needs one more lift of the same shape
    before it can use this: its [canon_fit] premise gives [fit_from p segs ..], and the goal after
    [run_init] is over [run_segments ..].  [fit_from] quantifies over [canon_reach], so it takes the
    same walk-bounded induction as [uniform_lift] (NOT a change to [canon_fit], which would shift
    an obligation rather than discharge it). *)
Theorem uniform_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  @YK15.realizes segs AcfgMode (init_config segs pc ph sp brk mb rnd lim inp) T ->
  YK15.cut_free segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  uniform segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  uniform (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H HC HU.
  assert (Hr : rom_ext (ms_rom (cfg_ms (init_config segs pc ph sp brk mb rnd lim inp)))
                 (seg_rom1 (run_segments segs inp sp mb)))
    by (rewrite init_config_rom; apply rom_ext_run_segments).
  rewrite init_config_run_segments. unfold run_segments at 1.
  apply (uniform_lift segs (vdso_segments (in_kernel inp) sp mb)
           (fun s Hs => vdso_segments_nx _ _ _ s Hs) (fun s Hs => vdso_segments_nw _ _ _ s Hs)
           Hvi _ T H HC HU _ Hr).
Qed.
End UniformRun.
